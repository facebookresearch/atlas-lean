---
article_id: af_7292c819ff72ca0f7f3f1c7f
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.TimeM.boyerMooreMatches_eq_naiveMatches
---

# Boyer Moore Matches eq naive Matches

Boyer-Moore and the canonical naive matcher return the same ordered list.
This is a result specification bridge, not a naive execution path.

## Depends on

- [Boyer Moore Matches](boyer-moore-matches.md)
- [Naive Matches](../../naive/naive-matches.md)

## Proof depends on

- [Match At](../../basic/match-at.md)
- [Boyer Moore Matches pairwise](boyer-moore-matches-pairwise.md)
- [Mem boyer Moore Matches iff](mem-boyer-moore-matches-iff.md)
- [Mem naive Matches iff](../../naive/mem-naive-matches-iff.md)
- [Naive Matches pairwise](../../naive/naive-matches-pairwise.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.StringMatching.BoyerMoore.Basic](../../../../../../../sources/v2/CSLibExt.md)
