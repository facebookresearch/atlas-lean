---
article_id: af_75e51d357a3d1d515dc903be
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.applySplit
---

# Apply Split

Exact split replacement on dimension lists: the last `c` copies of `a + b`
are replaced in place by `c` copies of `a` followed by `c * q ^ a` copies of `b`.
No sorting is performed; sortedness is checked separately at every stage.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Remove First NPos](remove-first-npos.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.RestrictedGaussianPartition](../../../../../sources/v2/MathlibExt.md)
