---
article_id: af_16cf40ec46f9a1bcb2aa8618
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.TimeM.lowerBound
---

# Lower Bound

Returns the first index containing a value at least `key`, charging one tick for each element
comparison. If every value is below `key`, it returns `xs.size`.

Precondition: `xs` must be sorted (or at least partitioned at `key`: every element below the
returned index is `< key` and every element from that index on is `≥ key`). On an unsorted array
the result is unspecified: for example, `lowerBound #[2, 1] 2` returns `2`, not the first
qualifying index `0`.

## Depends on

This node has no prerequisites.

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Search.LowerBound](../../../../../../sources/v2/CSLibExt.md)
