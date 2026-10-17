---
article_id: af_b9a7f02a24683076771ec3c2
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.SuffixArray.take_eq_of_le_lcp
---

# Take eq of le lcp

Any shorter prefix length also agrees: truncating the common prefix
of length `lcp x y` at `q ≤ lcp x y` still gives equal prefixes.

## Depends on

- [Lcp](lcp.md)

## Proof depends on

- [Take lcp eq](take-lcp-eq.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.SuffixArray](../../../../../../../sources/v2/CSLibExt.md)
