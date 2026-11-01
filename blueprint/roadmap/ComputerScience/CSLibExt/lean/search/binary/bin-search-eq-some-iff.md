---
article_id: af_b1c5dad1f397df284f1183ad
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.binSearch_eq_some_iff
---

# Bin Search eq some iff

On a sorted array, bounded binary search returns `a` exactly when `a` is the key and the key
occurs at a valid index between the inclusive raw bounds. The validity condition on the index
expresses the implementation's clamping of an oversized upper bound.

## Depends on

This node has no prerequisites.

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Search.Binary](../../../../../../sources/v2/CSLibExt.md)
