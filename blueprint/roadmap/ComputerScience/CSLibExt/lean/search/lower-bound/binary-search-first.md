---
article_id: af_ba244b2097e18904f4a570fc
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.TimeM.binarySearchFirst?
---

# Binary Search First?

Returns the first index containing `key`, or `none` when `key` is absent. A valid lower-bound index
costs one additional equality comparison.

Precondition: as for `lowerBound`, `xs` must be sorted (or partitioned at `key`); on an unsorted
array a present key can be missed and the result can be `none`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Lower Bound](lower-bound.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Search.LowerBound](../../../../../../sources/v2/CSLibExt.md)
