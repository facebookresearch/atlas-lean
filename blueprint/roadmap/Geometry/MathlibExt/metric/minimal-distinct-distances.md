---
article_id: af_c9a9cda05116ab9688c226ed
declaration: def
origin: cited
statement: formalized
lean: minimalDistinctDistances
---

# Minimal Distinct Distances

The minimum number of distinct distances determined by a set of `n` points in `X`.
The explicit existence witness prevents an empty candidate set, so the infimum is never
taken silently over `∅` (where `Nat.sInf_empty = 0` would apply).

## Depends on

This node has no prerequisites.

## Proof depends on

- [Distinct Distances](distinct-distances.md)

## Sources

- [MathlibExt, MathlibExt.Geometry.Metric](../../../../sources/v2/MathlibExt.md)
