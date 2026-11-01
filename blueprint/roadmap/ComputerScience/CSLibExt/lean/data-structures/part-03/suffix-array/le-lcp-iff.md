---
article_id: af_7d86b427c597e98bae96084a
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.SuffixArray.le_lcp_iff
---

# Le lcp iff

Maximality of `lcp`: `q` is below the longest-common-prefix length
exactly when it fits in both lists and their first `q` elements agree.
In particular clients can derive `q ≤ lcp x y` from prefix agreement
without unfolding the recursion (a constant-zero function would not
satisfy this).

## Depends on

- [Lcp](lcp.md)

## Proof depends on

- [Take eq of le lcp](take-eq-of-le-lcp.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.SuffixArray](../../../../../../../sources/v2/CSLibExt.md)
