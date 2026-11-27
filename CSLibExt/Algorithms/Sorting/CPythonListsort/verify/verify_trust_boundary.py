#!/usr/bin/env python3
"""Audit the integrated production/test boundary for CPython listsort."""
from __future__ import annotations
import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[3]
TEST = REPO / 'CSLibExtTest/Algorithms/Sorting/CPythonListsort'
EXPECTED = {
    'Transcription/MergeAt.lean': ['mergeAt_slide_regression'],
    'Correctness/MergeAtCorrectness.lean': ['mergeAt_thirdLast_slide_regression'],
    'Correctness/FoundNewRunCorrectness.lean': ['foundNewRunLoop_taken_merge_regression'],
    'Correctness/MergeForceCollapseCorrectness.lean': ['mergeForceCollapse_threeRun_equalKey_payload_regression'],
    'Correctness/ScanStepCorrectness.lean': ['listSortScan_long_run_no_extension_regression', 'listSortScan_policy_merge_then_push_regression'],
    'Correctness/ListSortCorrectness.lean': ['listSort_forward_keyed_duplicate_exact_regression', 'listSort_reverse_keyed_duplicate_exact_regression'],
    'Assembly/MergeMemorySafety.lean': ['listSort_mergeMemory_lo_event_regression', 'listSort_mergeMemory_hi_event_regression', 'listSort_mergeMemory_released_growth_regression'],
    'Assembly/PowerSortCostRegression.lean': ['listSort_powerSort_cost_rotation_regression'],
}

# SHA-256 of each UTF-8 proposition (outer whitespace removed) in the public
# pre-migration Atlas/CPythonListsort tree at 59590b8eaecc2f30a1f75f2c9d2000c1fb44a361.
# The migration map records those propositions but is not the baseline.
PINNED_PROPOSITION_SHA256 = {
    'foundNewRunLoop_taken_merge_regression':
        'a0c7a43e4bb9499ac19aabc25d0bde46b68f475ecc75f7d30fafaea01f5af7a8',
    'listSortScan_long_run_no_extension_regression':
        'e037e101663e555e89c85501334e9762718c462b6fecb0ccd0d0a4f515743fad',
    'listSortScan_policy_merge_then_push_regression':
        '37d33b6fb1e6c65590e799847917bced26684cf61e13485e129ac59ff7228c7c',
    'listSort_forward_keyed_duplicate_exact_regression':
        'd7f3519a1f3559947695642245a3affbfa861b0971b56c0ebc69c55ffbdad53b',
    'listSort_mergeMemory_hi_event_regression':
        '2bde73caf5b41b0120eb504ff4bac4c1f9fcc9c1f688aded9171febf50f23c62',
    'listSort_mergeMemory_lo_event_regression':
        '4b6f6a07b5897ff5b22763becab5f981227f30a010577678961b41a88fb59322',
    'listSort_mergeMemory_released_growth_regression':
        '610fe0edaf2ff06cb0d5b3cad92fdc73342eebb5e883fd4732f1f286bffb0133',
    'listSort_powerSort_cost_rotation_regression':
        'bb8fb3f4c1ec375403cf1d30e100e7bcc85d169d91b79303f2f8c90258fc903e',
    'listSort_reverse_keyed_duplicate_exact_regression':
        '3770ed28fa8e89018ed85855e2624e6ca29c1330c2ad97199178ac2157f7fbde',
    'mergeAt_slide_regression':
        'b58c292761428fc01f5b5c9547d0888c2e2ccf09787251e236c3094c90cc6d5a',
    'mergeAt_thirdLast_slide_regression':
        '82e58243a4566528c82714e0b4c613772d3651bc0bb4b80dbc3a8158f154e2e0',
    'mergeForceCollapse_threeRun_equalKey_payload_regression':
        '01de6f0355171457116772a79f526c80c7acd22f793bbe8527f8db431916e6ca',
}


def read_pinned_propositions(path: Path) -> dict[str, str]:
    names = {name for module_names in EXPECTED.values() for name in module_names}
    if set(PINNED_PROPOSITION_SHA256) != names:
        raise ValueError('pinned baseline must cover exactly the twelve original witnesses')
    record = json.loads(path.read_text(encoding='utf-8'))
    items = record.get('runtime_regressions') if isinstance(record, dict) else None
    if not isinstance(items, list) or len(items) != len(names):
        raise ValueError('regression record must contain exactly the twelve original witnesses')
    propositions = {}
    for item in items:
        if not isinstance(item, dict):
            raise ValueError('regression record entries must be objects')
        name = item.get('name')
        if not isinstance(name, str) or name not in names or name in propositions:
            raise ValueError('regression record must name each original witness exactly once')
        proposition = item.get('original_proposition')
        expected = PINNED_PROPOSITION_SHA256[name]
        if (not isinstance(proposition, str)
                or item.get('original_proposition_sha256') != expected
                or hashlib.sha256(proposition.strip().encode('utf-8')).hexdigest() != expected):
            raise ValueError(f'{name}: original proposition does not match the pinned baseline')
        propositions[name] = proposition
    return propositions


def main() -> int:
    errors = []
    try:
        propositions = read_pinned_propositions(ROOT / 'verify/migration-map.json')
    except (OSError, ValueError) as error:
        print(f'cannot read regression disposition record: {error}', file=sys.stderr)
        return 1
    production = sorted(ROOT.rglob('*.lean')) + [ROOT.with_suffix('.lean')]
    tests = sorted(TEST.rglob('*.lean')) + [TEST.with_suffix('.lean')]
    all_texts = {}
    for path in production + tests:
        if not path.is_file():
            errors.append(f'missing Lean module: {path.relative_to(REPO)}')
            continue
        text = path.read_text(encoding='utf-8')
        all_texts[path] = text
        for line_no, line in enumerate(text.splitlines(), 1):
            if 'native_decide' in line:
                errors.append(f'{path.relative_to(REPO)}:{line_no}: forbidden proof shortcut')
            if re.match(r'^\s*(?:public\s+)?import\s+Code(?:\.|\s|$)', line):
                errors.append(f'{path.relative_to(REPO)}:{line_no}: old generic module import')
            if path in production and re.match(r'^\s*(?:public\s+)?import\s+CSLibExtTest(?:\.|\s|$)', line):
                errors.append(f'{path.relative_to(REPO)}:{line_no}: production imports tests')
    prod_corpus = '\n'.join(all_texts.get(p, '') for p in production)
    for relative, names in EXPECTED.items():
        text = all_texts.get(TEST / relative, '')
        for name in names:
            if not re.search(r'^def\s+' + re.escape(name) + r'\s*:\s*IO Unit\s*:=', text, re.M):
                errors.append(f'{relative}: {name} must be an IO witness, not a theorem')
            assertion = re.search(
                r'(?ms)^def\s+' + re.escape(name) +
                r'\s*:\s*IO Unit\s*:=\s*CPythonListsortTest\.assertTrue\s+"' +
                re.escape(name) + r'"\s+\(decide\s+\(\s*(.*?)\)\)\s*\n#eval\s+' +
                re.escape(name) + r'\s*$', text)
            if assertion is None:
                errors.append(f'{relative}: {name} must assert its original predicate')
            elif re.sub(r'\s+', ' ', assertion.group(1).strip()) != re.sub(
                    r'\s+', ' ', propositions.get(name, '').strip()):
                errors.append(f'{relative}: {name} changed its original predicate')
            if len(re.findall(r'^#eval\s+' + re.escape(name) + r'\s*$', text, re.M)) != 1:
                errors.append(f'{relative}: {name} must have one asserting execution')
            if re.search(r'\b' + re.escape(name) + r'\b', prod_corpus):
                errors.append(f'{name}: executable witness leaked into the production corpus')
    if errors:
        print('CPython integration boundary failed:', file=sys.stderr)
        for error in errors: print('  - ' + error, file=sys.stderr)
        return 1
    print('verified CPython integration boundary: no proof shortcuts or old Code imports; '
          '12 asserting IO witnesses in tests, no production consumers')
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
