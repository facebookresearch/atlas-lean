---
article_id: af_03dae351902d6725a5c5a9fc
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.RangeTree.bounds_mem_toList_of_ne_nil
---

# Bounds mem to List of ne nil

The cached bounds of a nonempty bounds-valid tree are attained by
leaves, so `[tmin, tmax]` is the true leaf interval, not merely an
enclosing interval.

## Depends on

- [Range Tree](range-tree.md)
- [Bounds Ok](bounds-ok.md)
- [Tmax](tmax.md)
- [Tmin](tmin.md)
- [To List](to-list.md)

## Proof depends on

- [To List node](to-list-node.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.RangeTree](../../../../../../../../sources/v2/CSLibExt.md)
