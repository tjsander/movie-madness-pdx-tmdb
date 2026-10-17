#!/usr/bin/env python3
"""Finds the TMDB id behind each rental's poster and writes it to catalog/ as
`tmdb`: "movie/201085", "tv/13859", or None, with `tmdb_source`: "poster",
"description", "edition", "credits", "language", "title" or "manual".

The store's covers are TMDB posters under their TMDB file names (`poster`,
from fetch_media.py or update_catalog.py). TMDB can't look a poster up by
name, so for each distinct poster this searches TMDB for the titles that use
it and takes the result with that exact poster: first among the search
results' own posters; then, since the store's descriptions are TMDB's
overviews, a result whose overview is the rental's description; then in the
top results' full poster lists, since the store's copy may no longer be the
one TMDB shows first.

A poster match is the entry the store linked the title to, exactly; where the
store linked the wrong one, so does this. TMDB has since dropped some posters
the store still shows; those fall back to the single search result with the
shelf's director or actor in its credits (tmdb_source "credits"), or with the
same title and year (tmdb_source "title").

The store shows the wrong cover on a few percent of rentals, so every id is
checked against the titles TMDB has for it (tmdb-titles.jsonl): an id whose
titles are nothing like the rental's is dropped and kept as `tmdb_rejected`.

The store's data is not the last word: overrides.csv, beside this script, lists
titles it gets wrong or that can't be found from it, with the right TMDB id
(tmdb_source "manual"). It is applied after everything else.

Rentals with no usable cover are searched by title and settled by what else is
known: the shelf's director or actor being in the credits (tmdb_source
"credits"), the shelf's language with the year and a fitting title
("language"), or the same title and year ("title"). Those results are kept in
tmdb-by-title.jsonl. Where a match shows TMDB itself is probably wrong (an
entry made in the shelf's country but listed under another language), it is
listed in tmdb-corrections.csv to submit to TMDB.

A rental still without an id takes the one its other editions have: rentals
with the same title and year, when they agree (tmdb_source "edition").

Results are kept in tmdb-posters.jsonl, one line per poster, so a rerun only
looks up new posters. The TMDB token (API Read Access Token) is read from
~/.config/mmboxmonkey/tmdb-token.

  --max N    stop after N TMDB requests
  --retry    look up posters again that found nothing before
  --retry-titles   search again only for the titles that found nothing before
"""
import csv, difflib, fcntl, glob, html, json, os, re, sys, threading, time, unicodedata, urllib.error, urllib.parse, urllib.request
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed
from build_shelves import search_query
from scrape_shelves import arg, load_jsonl, log
from update_catalog import write_json

TOKEN_FILE = os.path.expanduser('~/.config/mmboxmonkey/tmdb-token')
RESULTS, TITLES, BY_TITLE = 'tmdb-posters.jsonl', 'tmdb-titles.jsonl', 'tmdb-by-title.jsonl'
CORRECTIONS = 'tmdb-corrections.csv'   # what looks wrong on TMDB itself, to submit there
API = 'https://api.themoviedb.org/3/'
PAUSE, LISTS = 0.05, 6   # seconds between a worker's requests; poster lists to open per poster
WORKERS = 6              # about 25 requests a second in all; TMDB allows around 50 per IP

# Foreign shelves by country -> TMDB original-language codes.
LANGUAGES = {
    'French': 'fr', 'Japanese': 'ja', 'Japanese Horror': 'ja', 'Samurai Films': 'ja', 'Chinese / Hong Kong': 'zh cn',
    'Italian': 'it', 'German': 'de', 'Spanish': 'es ca eu gl', 'Latin American': 'es pt', 'Korean': 'ko',
    'Russian': 'ru', 'Swedish': 'sv', 'Danish': 'da', 'Polish': 'pl', 'Czech': 'cs sk', 'Czech Animation': 'cs sk',
    'Indian': 'hi ta te bn ml kn mr pa', 'Iranian': 'fa', 'Dutch': 'nl', 'Finnish': 'fi', 'Hungarian': 'hu',
    'Norwegian': 'no nb', 'Greek': 'el', 'Turkish': 'tr', 'Thai': 'th', 'Brazilian': 'pt', 'Portuguese': 'pt',
    'Israeli': 'he', 'Vietnamese': 'vi', 'Yugoslavian': 'sr hr sh sl mk bs', 'Romanian': 'ro', 'Icelandic': 'is',
    'Filipino': 'tl', 'Indonesian': 'id', 'Belgian': 'fr nl', 'Swiss': 'fr de it',
}

# The same shelves -> production country codes, for when TMDB's language looks wrong.
COUNTRIES = {
    'French': 'FR BE CH', 'Japanese': 'JP', 'Japanese Horror': 'JP', 'Samurai Films': 'JP',
    'Chinese / Hong Kong': 'CN HK TW', 'Italian': 'IT', 'German': 'DE AT CH DD', 'Spanish': 'ES',
    'Latin American': 'MX AR BR CL CO CU PE UY VE BO EC PY CR GT DO PA', 'Korean': 'KR', 'Russian': 'RU SU',
    'Swedish': 'SE', 'Danish': 'DK', 'Polish': 'PL', 'Czech': 'CZ CS XC SK', 'Czech Animation': 'CZ CS XC SK',
    'Indian': 'IN', 'Iranian': 'IR', 'Dutch': 'NL BE', 'Finnish': 'FI', 'Hungarian': 'HU', 'Norwegian': 'NO',
    'Greek': 'GR', 'Turkish': 'TR', 'Thai': 'TH', 'Brazilian': 'BR', 'Portuguese': 'PT', 'Israeli': 'IL',
    'Vietnamese': 'VN', 'Yugoslavian': 'YU RS HR SI BA MK ME', 'Romanian': 'RO', 'Icelandic': 'IS',
    'Filipino': 'PH', 'Indonesian': 'ID', 'Belgian': 'BE', 'Swiss': 'CH',
}
SEASON = re.compile(r'\b(season|series)\s*\d+|\b\d+(st|nd|rd|th)\s+season|\bcomplete\s+(series|season)'
                    r'|\b(season|series)\s+(one|two|three|four|five|six|seven|eight|nine|ten)\b|\bfinal\s+season', re.I)

EPISODE = re.compile(r'\bEp\.\s*', re.I)
# Among several results of one title and year: the only one from the very year needs
# YEAR_VOTES TMDB votes; a clear favourite FAVOURITE votes and that many times the next one's.
YEAR_VOTES, FAVOURITE, TIMES = 10, 300, 10

def rental_years(e):
    """The years a rental's film may be from: the catalog's, and any that staff put
    in its title ("Departed, The (2006) (Blu-Ray)", which the catalog dates 2009,
    the disc's year)."""
    return list(dict.fromkeys([int(y) for y in e.get('year') or [] if y.isdigit()] + named_years(e)))

def named_years(e):
    """The years in a rental's title."""
    return [int(y) for y in re.findall(r'\((\d{4})\b', html.unescape(e['title']['rendered'])) if 1880 <= int(y) <= 2100]

OVERRIDES = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'overrides.csv')

def load_overrides():
    """{title: [(year or None, tmdb or None)]} from overrides.csv, our own corrections
    for where the store's data leads to the wrong film or to none. A row applies to
    every rental of that title (compared without parentheses, case or punctuation),
    and of that year when it gives one; a blank tmdb says the rental has no entry."""
    rows = defaultdict(list)
    if os.path.exists(OVERRIDES):
        for r in csv.DictReader(open(OVERRIDES, newline='')):
            if r.get('title'):
                rows[plain(r['title'])].append((int(r['year']) if (r.get('year') or '').strip().isdigit() else None,
                                                (r.get('tmdb') or '').strip() or None))
    return rows

def override(e, rows):
    """(True, tmdb) when a row of overrides.csv covers this rental, else (False, None)."""
    for year, tmdb in rows.get(edition_key(e)[0], ()):
        if year is None or year in rental_years(e):
            return True, tmdb
    return False, None

class Stop(Exception):
    pass

def whole(title):
    """A catalog title without what the store's 60-character limit cut short, a
    parenthesis left open ("... (Limited Ed.) (DVD) (OOP"), or a trailing "OOP"."""
    return re.sub(r'\s*(\([^)]*|\bOOP!*)\s*$', '', html.unescape(title))

def queries(title):
    """Searches to try for one catalog title, most specific first."""
    q = search_query(whole(title))
    first = q.split('/')[0].strip()   # double features: the first film
    series = re.sub(r'\s+[–-]?\s*(Vol\.?|Volume|Season|Series|Set|Collection|Complete|Disc)\b.*', '', first, flags=re.I).strip(' –-')
    return [v for v in dict.fromkeys([q, first, series, re.sub(r'\s+\d{4}$', '', series)]) if v]

ODD_LETTERS = str.maketrans({'ø': 'o', 'ł': 'l', 'đ': 'd', 'ß': 'ss', 'æ': 'ae', 'œ': 'oe', 'ð': 'd', 'þ': 'th', 'ı': 'i'})

def fold(text):
    """Lower case without accents: "François" and "FRANCOIS" alike."""
    t = unicodedata.normalize('NFKD', text.casefold().translate(ODD_LETTERS))
    return ''.join(c for c in t if not unicodedata.combining(c))

def plain(title):
    """A title for comparing: letters and digits only, no accents, "&" as "and"."""
    return re.sub(r'[^a-z0-9]+', '', fold(title).replace('&', 'and'))

def name_words(name):
    return frozenset(re.findall(r'[a-z0-9]+', fold(name)))

def same_person(person, credit):
    """Whether a shelf's person (a set of name words) is a credited name. Word order
    doesn't count ("PARK, CHAN-WOOK" is "Park Chan-wook"), a credit may be longer
    ("LEE, DANNY" is "Danny Lee Sau-Yin"), initials may be missing, and spellings may
    differ a little ("PARADJANOV" is "Parajanov")."""
    core = frozenset(w for w in person if len(w) > 1) or person
    if core <= credit:
        return True
    a, b = ''.join(sorted(person)), ''.join(sorted(credit))
    return len(credit) > 1 and abs(len(a) - len(b)) <= 2 and difflib.SequenceMatcher(None, a, b).ratio() >= 0.88

def tmdb_titles(api, tmdb):
    """Every title TMDB lists for an entry: its own, the original, alternatives and translations."""
    d = api(tmdb, append_to_response='alternative_titles,translations')
    alt = d.get('alternative_titles', {})
    found = [d.get('title'), d.get('name'), d.get('original_title'), d.get('original_name')]
    found += [t.get('title') for t in alt.get('titles', []) + alt.get('results', [])]
    found += [t.get('data', {}).get(k) for t in d.get('translations', {}).get('translations', []) for k in ('title', 'name')]
    return list(dict.fromkeys(t for t in found if t))

ARTICLE = re.compile(r'^(the|a|an|le|la|les|l|el|los|las|il|lo|i|gli|der|die|das|un|une|una|uno)\s+', re.I)
NUMBERS = {w: str(n) for n, ws in enumerate((
    'one i', 'two ii', 'three iii', 'four iv', 'five v', 'six vi', 'seven vii', 'eight viii', 'nine ix', 'ten x',
    'eleven xi', 'twelve xii', 'thirteen xiii', 'fourteen xiv', 'fifteen xv'), 1) for w in ws.split()}

def loose(title):
    """A title for checking a link: no leading article, and numbers as digits however
    written ("Part II", "Part Two", "Part 2"; "04" as "4")."""
    t = ARTICLE.sub('', title.strip().casefold())
    t = re.sub(r'[a-z]+|\d+', lambda m: NUMBERS.get(m.group(), m.group().lstrip('0') or '0'), t)
    return plain(t)

def title_fits(title, tmdb_titles):
    """Whether a catalog title is plausibly one of a TMDB entry's titles. The store
    shows the wrong cover on a few percent of rentals, and a poster match then
    finds the wrong film; those have titles nothing alike."""
    t = whole(title)
    parts = [t] + re.split(r'\s*/\s*', re.sub(r'\([^)]*\)', '', t))   # each half of a double feature
    ours = {loose(q) for part in parts for q in queries(part)} - {''}
    theirs = {loose(x) for x in tmdb_titles} - {''}
    if ours & theirs:
        return True
    for a in ours:
        for b in theirs:
            if min(len(a), len(b)) >= 6 and (a in b or b in a):
                return True
            if (abs(len(a) - len(b)) <= 0.3 * max(len(a), len(b)) and re.findall(r'\d+', a) == re.findall(r'\d+', b)
                    and difflib.SequenceMatcher(None, a, b).ratio() >= 0.85):
                return True
    return False

def shelf_countries(e):
    """Production country codes that fit a rental's foreign shelf."""
    parts = (e.get('shelf') or '').split(' > ')
    return set(COUNTRIES.get(parts[1], '').split()) if len(parts) > 1 and parts[0] == 'Foreign' else set()

def write_corrections():
    """Lists what looks wrong on TMDB itself, to submit there: entries matched by title,
    year and production country whose original language is neither the country's nor
    one TMDB says is spoken in them."""
    # Co-productions are often rightly in another language (a Haneke film in French on
    # the German shelf). Listed are only those where TMDB disagrees with itself: the
    # original language isn't one it says is spoken, and the shelf's language is.
    rows = {r['tmdb']: r['tmdb_error'] for r in load_jsonl(BY_TITLE) if r.get('tmdb_error') and r.get('tmdb')
            and r['tmdb_error']['now'] not in r['tmdb_error']['spoken']
            and set(r['tmdb_error']['expected']) & set(r['tmdb_error']['spoken'])}
    with open(CORRECTIONS, 'w', newline='') as out:
        w = csv.writer(out)
        w.writerow(['tmdb', 'url', 'title', 'year', 'field', 'value on TMDB', 'expected', 'production countries',
                    'spoken languages', 'Movie Madness shelf'])
        for tmdb, x in sorted(rows.items(), key=lambda kv: (kv[1]['shelf'] or '', kv[1]['title'] or '')):
            w.writerow([tmdb, f'https://www.themoviedb.org/{tmdb}', x['title'], x['year'], x['field'], x['now'],
                        ' or '.join(x['expected']), ' '.join(x['countries']), ' '.join(l for l in x['spoken'] if l), x['shelf']])
    log(f'{len(rows)} possible TMDB errors listed in {CORRECTIONS}')

def shelf_people(e):
    """The directors or actors a rental is shelved under, each a set of name words:
    one from "LAST, FIRST (WRITTEN BY)", two from "COEN, ETHAN AND JOEL". None for
    shelves that only look like names ("COREYS, THE")."""
    level = (e.get('shelf') or '').rsplit(' > ', 1)[-1] if ' > ' in (e.get('shelf') or '') else ''
    if ',' not in level or level.upper() != level:
        return []
    last, first = re.sub(r'\(.*', '', level).split(',', 1)
    firsts = [f for f in re.split(r'\s+(?:AND|&)\s+', first.strip()) if f.strip()]
    if not firsts or first.strip() in ('THE', 'A', 'AN'):
        return []
    return [name_words(f + ' ' + last) for f in firsts]

def shelf_person(e):
    """The same as one string, for lookup_key."""
    return '+'.join(sorted(''.join(sorted(p)) for p in shelf_people(e))) or None

def shelf_languages(e):
    """TMDB language codes for a rental on a foreign country's shelf; none for English-speaking ones."""
    parts = (e.get('shelf') or '').split(' > ')
    return set(LANGUAGES.get(parts[1], '').split()) if len(parts) > 1 and parts[0] == 'Foreign' else set()

def lookup_key(e):
    """What one title search serves: the title and year, and the shelf's person and languages."""
    title, year = edition_key(e) if e.get('year') else (edition_key({**e, 'year': []})[0], ())
    return '|'.join([title, ','.join(year), shelf_person(e) or '', ','.join(sorted(shelf_languages(e)))])

def edition_key(e):
    """What editions of one film share: its title without the parentheses, and its year."""
    return plain(re.sub(r'\([^)]*\)', '', whole(e['title']['rendered']))), tuple(e['year'])

def words(description):
    """A description for comparing; '' when too short to identify anything."""
    w = re.sub(r'[^a-z0-9]+', ' ', (description or '').casefold()).strip()
    return w if len(w) >= 40 else ''

def same_text(overview, texts):
    """Whether a TMDB overview is one of the store's descriptions, give or take small edits."""
    o = words(overview)
    return bool(o) and any(o == t or abs(len(o) - len(t)) < 0.2 * len(t)
                           and difflib.SequenceMatcher(None, t, o).ratio() >= 0.9 for t in texts)

def source(how):
    return {'title and year': 'title', 'alternative title': 'title', 'title and exact year': 'title',
            'title, year and votes': 'title', 'description': 'description', 'credits': 'credits',
            'language': 'language'}.get(how, 'poster')

def main():
    if not os.path.exists(TOKEN_FILE):
        log(f'no TMDB token at {TOKEN_FILE}; skipping')
        return
    token = open(TOKEN_FILE).read().strip()
    lock = open(RESULTS, 'a')   # held until exit, so a second run (the daily update) skips
    try:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        log('another resolve_tmdb.py is running; skipping')
        return
    max_req, stats = int(arg('--max') or 0), {'requests': 0}
    counting = threading.Lock()

    # Answers are kept for the run: the poster and title passes often ask the
    # same search, credits or images again (editions share titles, and a
    # candidate turns up for several posters). Only real answers are kept;
    # errors are retried as before.
    memo, memo_lock = {}, threading.Lock()

    def api(path, **params):
        key = (path, tuple(sorted(params.items())))
        with memo_lock:
            if key in memo:
                stats['cached'] = stats.get('cached', 0) + 1
                return memo[key]
        result = fetch(path, **params)
        with memo_lock:
            memo[key] = result
        return result

    def fetch(path, **params):
        if max_req and stats['requests'] >= max_req:
            raise Stop(f'reached {max_req} requests')
        url = API + path + ('?' + urllib.parse.urlencode(params) if params else '')
        for attempt in range(4):
            time.sleep(PAUSE if attempt == 0 else 5 * attempt)
            with counting:
                stats['requests'] += 1
            try:
                req = urllib.request.Request(url, headers={'Authorization': 'Bearer ' + token, 'Accept': 'application/json'})
                return json.load(urllib.request.urlopen(req, timeout=30))
            except urllib.error.HTTPError as ex:
                if ex.code == 404:
                    return {}
                if ex.code == 401:
                    raise Stop('TMDB rejected the token')
                log(f'  error {ex.code} on {path}')
            except Exception as ex:
                log(f'  error {ex} on {path}')
        raise Stop(f'giving up on {path}')

    def credits_have(key, people):
        """Whether any of a shelf's people is in a TMDB entry's cast or crew."""
        credits = api(key + ('/credits' if key.startswith('movie') else '/aggregate_credits'))
        names = {name_words(p.get('name') or '') for p in credits.get('cast', []) + credits.get('crew', [])}
        return any(same_person(who, n) for who in people for n in names)

    def resolve(poster, entries):
        """(tmdb, how) for one poster, from the titles of the rentals that use it."""
        want, candidates = '/' + poster, {}
        texts = {words(descriptions.get(e['id'])) for e in entries} - {''}
        years = {y for e in entries for y in e.get('year') or []}
        tried = set()
        for e in entries[:3]:
            for q in queries(e['title']['rendered']):
                if q.casefold() in tried:
                    continue
                tried.add(q.casefold())
                results = [r for r in api('search/multi', query=q, include_adult='true').get('results', [])
                           if r.get('media_type') in ('movie', 'tv')]
                for r in results:
                    if r.get('poster_path') == want:
                        return f'{r["media_type"]}/{r["id"]}', 'search'
                for r in results:   # the store's descriptions are TMDB's overviews, and search results carry them
                    if same_text(r.get('overview'), texts):
                        return f'{r["media_type"]}/{r["id"]}', 'description'
                for r in results:
                    key = f'{r["media_type"]}/{r["id"]}'
                    candidates.setdefault(key, ((r.get('release_date') or r.get('first_air_date') or '')[:4],
                                                {plain(r.get(k) or '') for k in ('title', 'name', 'original_title', 'original_name')}))
        by_year = sorted(candidates, key=lambda k: candidates[k][0] not in years)   # stable: TMDB's order within each
        for key in by_year[:LISTS]:
            if any(p.get('file_path') == want for p in api(key + '/images').get('posters', [])):
                return key, 'poster list'
        # TMDB has dropped some posters the store still shows. Then, as for rentals
        # with no cover: the one result with the shelf's director or actor in its
        # credits, or else the one with the same title and year that doesn't lack them.
        people, lacking = {p for e in entries for p in shelf_people(e)}, set()
        if people:
            hits = [k for k in by_year[:5] if credits_have(k, people) or lacking.add(k)]
            if len(hits) == 1:
                return hits[0], 'credits'
        same = [k for k, (year, titles) in candidates.items()
                if year in years and k not in lacking and titles & {plain(q) for q in tried}]
        return (same[0], 'title and year') if len(same) == 1 else (None, None)

    def title_rules(e, lacking):
        """(tmdb, how) for a rental with no usable cover, from a title search and what
        else is known about it. Each rule was checked against rentals with poster ids
        and disagreed with 2% of them at most. Read by hand, about 1 in 20 of the
        alternative-title matches among rentals with no other id were wrong; those
        found go in overrides.csv.
          credits   the one result with the shelf's director or actor in its credits
          language  the one result in the shelf's language, within a year, whose title fits
          title and year  the one result with the same title, within a year
          alternative title  the same, by a title TMDB lists for it but doesn't show
          title and exact year  of several, the only one from the very year
          title, year and votes  of several films (or shows) from the very year, the one far better known
        Between a film and shows of the same title and year, the film wins. A title
        naming a season or series only matches shows; a result whose credits
        lack the shelf's person is out; and on a foreign shelf a result in another
        language only counts if it was made in that country, in which case TMDB's
        language is probably wrong and the third value says so. Results refused for
        lacking the shelf's person are added to `lacking`."""
        found, years = {}, rental_years(e)
        asked = queries(e['title']['rendered'])
        asked += [v for v in dict.fromkeys(EPISODE.sub('Episode ', q) for q in asked) if v not in asked]
        for q in asked:
            for r in api('search/multi', query=q, include_adult='true').get('results', []):
                if r.get('media_type') in ('movie', 'tv'):
                    found.setdefault(f'{r["media_type"]}/{r["id"]}', (q, r))
            # The general search can bury a film under shows and people of the same
            # name ("Pride And Prejudice", "Wall-e"); asking for films of its year finds it.
            for y in () if SEASON.search(html.unescape(e['title']['rendered'])) else years:
                for r in api('search/movie', query=q, year=y, include_adult='true').get('results', []):
                    found.setdefault(f'movie/{r["id"]}', (q, r))
        def year_of(r):
            y = (r.get('release_date') or r.get('first_air_date') or '')[:4]
            return int(y) if y.isdigit() else None
        def near(r):
            return year_of(r) is not None and any(abs(year_of(r) - x) <= 1 for x in years)
        def votes(r):
            return r.get('vote_count') or 0
        def names(r):
            return [r[k] for k in ('title', 'name', 'original_title', 'original_name') if r.get(k)]
        ours = {loose(q) for q in asked}
        def film_first(hits):
            """Of a film and shows of the same title around the same year, the film, when
            it is the better known: a rental that could be either (or holds both cuts)
            is filed under the film."""
            films = [k for k in hits if k.startswith('movie/')]
            same = all(near(found[k][1]) and ours & {loose(x) for x in names(found[k][1])} for k in hits)
            # Not a film less known than the show: TMDB has stray film entries for miniseries.
            known = films and votes(found[films[0]][1]) >= max(votes(found[k][1]) for k in hits)
            return films if len(films) == 1 and len(hits) > 1 and same and known else hits
        # A title that names a season or series is a show, never a film of the same name.
        if SEASON.search(html.unescape(e['title']['rendered'])):
            found = {k: v for k, v in found.items() if k.startswith('tv/')}
        who = shelf_people(e)
        if who:
            # A result without them is not this shelf's film, whatever its title.
            hits = [k for k in sorted(found, key=lambda k: not near(found[k][1]))[:5]
                    if credits_have(k, who) or lacking.add(k)]
            hits = film_first(hits)
            if len(hits) == 1:
                return hits[0], 'credits', None
        langs = shelf_languages(e)
        if langs:
            hits = [k for k, (q, r) in found.items() if r.get('original_language') in langs and near(r)
                    and k not in lacking and title_fits(e['title']['rendered'], names(r))]
            if len(hits) == 1:
                return hits[0], 'language', None
        # The film itself, by title and year. TMDB may have it under another of its
        # titles ("Star Wars" for "Star Wars Episode IV: A New Hope"), so failing an
        # exact one, the best-known few results are checked against all of theirs.
        left = [k for k, (q, r) in found.items() if near(r) and k not in lacking]
        hits, how = [k for k in left if ours & {loose(x) for x in names(found[k][1])}], 'title and year'
        if not hits:
            # Only the title in full: cut down to a series' name ("Brotherhood" from
            # "Brotherhood: Season 3") it is too often some other show's other title.
            whole_title = {loose(asked[0]), loose(EPISODE.sub('Episode ', asked[0]))}
            hits = [k for k in sorted(left, key=lambda k: -votes(found[k][1]))[:3]
                    if whole_title & {loose(x) for x in tmdb_titles(api, k)}]
            how = 'alternative title'
        hits = film_first(hits)
        if len(hits) > 1:
            # Several of that title around that year, often a feature and a short: the
            # only one from the very year, or of several from it the far better known.
            ranked = sorted(hits, key=lambda k: -votes(found[k][1]))
            that_year = [k for k in hits if year_of(found[k][1]) in (named_years(e) or years)]   # the title's year, if it has one
            if len(that_year) == 1 and votes(found[that_year[0]][1]) == votes(found[ranked[0]][1]) >= YEAR_VOTES:
                hits, how = that_year, 'title and exact year'
            elif (ranked[0] in that_year and len({k.split('/')[0] for k in hits}) == 1
                  and votes(found[ranked[0]][1]) >= max(FAVOURITE, TIMES * votes(found[ranked[1]][1]))):
                hits, how = ranked[:1], 'title, year and votes'
        if len(hits) != 1:
            return None, None, None
        r = found[hits[0]][1]
        if langs and r.get('original_language') not in langs:
            # Same title and year but another language: a different film, unless TMDB has
            # the language wrong, which its production countries can show.
            d = api(hits[0])
            made_in = {c.get('iso_3166_1') for c in d.get('production_countries', [])} | set(d.get('origin_country') or [])
            if not made_in & shelf_countries(e):
                return None, None, None
            return hits[0], 'title and year', {
                'field': 'original_language', 'now': r.get('original_language'), 'shelf': e.get('shelf'),
                'expected': sorted(langs), 'countries': sorted(c for c in made_in if c),
                'spoken': [l.get('iso_639_1') for l in d.get('spoken_languages', [])],
                'title': d.get('title') or d.get('name'),
                'year': (d.get('release_date') or d.get('first_air_date') or '')[:4]}
        return hits[0], how, None

    def by_title(e):
        """title_rules' answer, with what to keep beside it: a likely TMDB error, and
        when nothing matched, the results refused for lacking the shelf's person."""
        lacking = set()
        tmdb, how, tmdb_error = title_rules(e, lacking)
        return tmdb, how, {**({'tmdb_error': tmdb_error} if tmdb_error else {}),
                           **({'lacking': sorted(lacking)} if lacking and not tmdb else {})}

    def catalog():
        return {f: json.load(open(f)) for f in glob.glob('catalog/page*.json')}

    descriptions = {r['id']: r['description'] for f in glob.glob('catalog-media/page*.json') for r in json.load(open(f))}
    descriptions.update((r['id'], r['description']) for r in load_jsonl('catalog-media/updates.jsonl'))

    by_poster = defaultdict(list)
    for es in catalog().values():
        for e in es:
            if e.get('poster'):
                by_poster[e['poster']].append(e)
    known, sources = {}, {}
    for r in load_jsonl(RESULTS):   # a later line for the same poster replaces an earlier one
        known[r['poster']], sources[r['poster']] = r['tmdb'], source(r['how'])
    todo = [p for p in by_poster if p not in known or '--retry' in sys.argv and known[p] is None]
    log(f'{len(by_poster)} distinct posters; {len(todo)} to look up')

    # WORKERS posters at a time; results are written here, in the order they finish.
    found, pool = 0, ThreadPoolExecutor(WORKERS)
    lookups = {pool.submit(resolve, p, by_poster[p]): p for p in todo}
    try:
        with open(RESULTS, 'a') as out:
            for n, done in enumerate(as_completed(lookups), 1):
                poster, (tmdb, how) = lookups[done], done.result()
                known[poster], sources[poster] = tmdb, source(how)
                found += bool(tmdb)
                out.write(json.dumps({'poster': poster, 'tmdb': tmdb, 'how': how}) + '\n')
                out.flush()
                if n % 1000 == 0:
                    log(f'  {n}/{len(todo)} posters, {found} matched, {stats["requests"]} requests')
        log('all posters looked up')
    except Stop as why:
        log(f'stopping: {why}')
    pool.shutdown(cancel_futures=True)

    # Every title TMDB has for each id found, to check the store's links against.
    titles = {r['tmdb']: r['titles'] for r in load_jsonl(TITLES)}
    need = sorted({t for t in known.values() if t} - set(titles))
    if need:
        log(f'{len(need)} TMDB entries to fetch titles for')
        pool = ThreadPoolExecutor(WORKERS)
        fetches = {pool.submit(tmdb_titles, api, t): t for t in need}
        try:
            with open(TITLES, 'a') as out:
                for n, done in enumerate(as_completed(fetches), 1):
                    titles[fetches[done]] = done.result()
                    out.write(json.dumps({'tmdb': fetches[done], 'titles': done.result()}, ensure_ascii=False) + '\n')
                    if n % 5000 == 0:
                        log(f'  {n}/{len(need)} entries, {stats["requests"]} requests')
        except Stop as why:
            log(f'stopping: {why}')
        pool.shutdown(cancel_futures=True)
    log(f'{found} matched by poster this run; {stats["requests"]} requests')

    def assign(pages):
        """Sets tmdb on every rental from its poster, then from its other editions."""
        rejected = copied = 0
        editions = defaultdict(set)   # (title, year) -> ids its rentals have
        for es in pages.values():
            for e in es:
                e['tmdb'] = known.get(e.get('poster'))
                e['tmdb_rejected'] = None
                if e['tmdb'] in titles and not title_fits(e['title']['rendered'], titles[e['tmdb']]):
                    e['tmdb'], e['tmdb_rejected'] = None, e['tmdb']   # the store's cover is another film's
                    rejected += 1
                e['tmdb_source'] = sources[e['poster']] if e['tmdb'] else None
                if e['tmdb'] and e.get('year'):
                    editions[edition_key(e)].add(e['tmdb'])
        # A rental with no id of its own takes the id of another edition: one with the
        # same title and year, when all of those that have an id agree on it. Rentals
        # on a director's or actor's shelf wait: their own search comes first, and
        # may have refused that very film for lacking the person.
        for es in pages.values():
            for e in es:
                if not e['tmdb'] and not shelf_people(e) and e.get('year') and len(editions.get(edition_key(e), ())) == 1:
                    (e['tmdb'],), e['tmdb_source'] = editions[edition_key(e)], 'edition'
                    copied += 1
        return rejected, copied, editions

    # Rentals still without an id (no cover, or the wrong one) are searched by title.
    pages = catalog()
    assign(pages)
    groups = {}
    for es in pages.values():
        for e in es:
            if not e['tmdb'] and (e.get('year') or shelf_person(e)):
                groups.setdefault(lookup_key(e), e)
    titled, refused = {}, {}   # a later line for the same key replaces an earlier one
    for r in load_jsonl(BY_TITLE):
        titled[r['key']], refused[r['key']] = (r['tmdb'], r['how']), set(r.get('lacking', ()))
    todo = [k for k in groups if k not in titled or titled[k][0] is None and ('--retry' in sys.argv or '--retry-titles' in sys.argv)]
    log(f'{len(groups)} titles without an id; {len(todo)} to search for')
    found, pool = 0, ThreadPoolExecutor(WORKERS)
    searches = {pool.submit(by_title, groups[k]): k for k in todo}
    try:
        with open(BY_TITLE, 'a') as out:
            for n, done in enumerate(as_completed(searches), 1):
                key, (tmdb, how, extra) = searches[done], done.result()
                titled[key], refused[key] = (tmdb, how), set(extra.get('lacking', ()))
                found += bool(tmdb)
                out.write(json.dumps({'key': key, 'tmdb': tmdb, 'how': how, **extra}, ensure_ascii=False) + '\n')
                out.flush()
                if n % 2000 == 0:
                    log(f'  {n}/{len(todo)} titles, {found} matched, {stats["requests"]} requests')
        log('all titles searched')
    except Stop as why:
        log(f'stopping: {why}')
    pool.shutdown(cancel_futures=True)
    log(f'{found} matched by title this run; {stats["requests"]} requests in all, {stats.get("cached", 0)} answered from this run\'s cache')

    write_corrections()

    # Read the catalog again before writing: a long run may overlap the daily update.
    pages = catalog()
    rejected, copied, editions = assign(pages)
    have = by_search = fixed = 0
    corrections = load_overrides()
    for f, es in pages.items():
        for e in es:
            tmdb, how = titled.get(lookup_key(e), (None, None)) if not e['tmdb'] else (None, None)
            if tmdb and tmdb != e['tmdb_rejected']:
                e['tmdb'], e['tmdb_source'] = tmdb, source(how)
                by_search += 1
            elif not e['tmdb'] and shelf_people(e) and e.get('year') and len(editions.get(edition_key(e), ())) == 1:
                (tmdb,) = editions[edition_key(e)]   # the edition copy they waited for
                if tmdb not in refused.get(lookup_key(e), ()):
                    e['tmdb'], e['tmdb_source'] = tmdb, 'edition'
                    copied += 1
            ours, tmdb = override(e, corrections)
            if ours:   # our own correction, whatever the store's data led to
                fixed += tmdb != e['tmdb']
                e['tmdb'], e['tmdb_source'] = tmdb, 'manual' if tmdb else None
            have += bool(e['tmdb'])
        write_json(f, es)
    log(f'tmdb written to the catalog: {have} rentals have one ({copied} from another edition, {by_search} by title search); '
        f'{rejected} dropped because the title is not one of the TMDB entry\'s; {fixed} set by overrides.csv')

if __name__ == '__main__':
    main()
