---
article_id: af_12d6e1fda1014f3cfacbb7ac
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.TimeM.boyerMooreMatches_time_replicate
---

# Boyer Moore Matches time replicate

Repeated-symbol inputs realize `m * (n - m + 1)` actual character tests.
The formula also includes conversions, preprocessing and the other selected events.

## Depends on

- [Preprocess](../preprocessing/preprocess.md)
- [Boyer Moore Matches](../basic/boyer-moore-matches.md)

## Proof depends on

- [Preprocess full Match](../preprocessing/preprocess-full-match.md)
- [Preprocess good Suffix](../preprocessing/preprocess-good-suffix.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.StringMatching.BoyerMoore.Complexity](../../../../../../../sources/v2/CSLibExt.md)
