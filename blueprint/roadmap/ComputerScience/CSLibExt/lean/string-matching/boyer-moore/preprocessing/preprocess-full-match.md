---
article_id: af_0421396e6bc2adf9867f790c
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.StringMatching.BoyerMoore.preprocess_fullMatch
---

# Preprocess full Match

The full-match shift is the least positive period of the pattern, so later
matcher stages may continue without discarding overlapping occurrences.

## Depends on

- [Preprocess](preprocess.md)

## Proof depends on

- [Preprocess good Suffix](preprocess-good-suffix.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.StringMatching.BoyerMoore.Preprocessing](../../../../../../../sources/v2/CSLibExt.md)
