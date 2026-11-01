---
article_id: af_d20271d630e661aa5274054e
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.IntervalTree.Tree.CacheInvariant
---

# Cache Invariant

Every cached field is exact, recursively: the cached maximum is an
attained upper bound, and the stored height and size equal the recursive
height (`max` of the child heights plus one) and size (sum of the child
sizes plus one) of the subtree.

## Depends on

- [Tree](tree.md)

## Proof depends on

- [Entry](entry.md)
- [Interval](interval.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.IntervalTree](../../../../../../../../sources/v2/CSLibExt.md)
