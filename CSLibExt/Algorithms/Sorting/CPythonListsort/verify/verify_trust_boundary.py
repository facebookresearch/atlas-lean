#!/usr/bin/env python3
"""Audit the integrated production/test boundary for CPython listsort."""
from __future__ import annotations
import re
import sys
import json
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

def main() -> int:
    errors = []
    try:
        record = json.loads((ROOT / 'verify/migration-map.json').read_text())
        propositions = {item['name']: item['original_proposition']
                        for item in record['runtime_regressions']}
    except (OSError, ValueError, KeyError) as error:
        print(f'cannot read regression disposition record: {error}', file=sys.stderr)
        return 1
    expected_names = {name for names in EXPECTED.values() for name in names}
    if set(propositions) != expected_names:
        errors.append('regression record must contain exactly the twelve original witnesses')
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
