---
article_id: af_ada719e79ec00e5bbfd382f2
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.StringMatching.computeZ_prefix_iff
---

# Compute Z prefix iff

Every returned entry is the maximal common-prefix length of its suffix.
The explicit suffix-length bound rules out equality caused by `List.take` truncation.

## Depends on

- [Compute Z](compute-z.md)

## Proof depends on

- [Compute Z zero](compute-z-zero.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.StringMatching.ZAlgorithm](../../../../../../sources/v2/CSLibExt.md)
