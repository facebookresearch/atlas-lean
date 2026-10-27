---
article_id: af_3248b325bdb3b72e6ea511e1
declaration: structure
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.IntervalTree.Cost
---

# Cost

Counts performed by the executable branches of an operation.

The `maxCacheReads` field is deliberately narrow: it counts only the
cached-maximum reads performed by search pruning in `searchWithCost`, one
per visited node where the left subtree's cached maximum decides the
descent. Maintenance paths (`mkNode`, `rebalanceWithCost`, and the
rotations) read cached heights, sizes, and maxima through constructor
patterns while rebuilding nodes; those field projections are not
separately instrumented, and maintenance work is reported through
`cacheWrites`, `rotations`, and the remaining counters instead.

## Depends on

This node has no prerequisites.

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.IntervalTree](../../../../../../../../sources/v2/CSLibExt.md)
