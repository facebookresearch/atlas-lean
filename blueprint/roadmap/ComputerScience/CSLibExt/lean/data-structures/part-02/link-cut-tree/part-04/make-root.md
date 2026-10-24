---
article_id: af_aa50a89c5f2c6def5aaf59fd
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.LinkCutTree.State.makeRoot
---

# Make Root

Reroot the represented tree containing `x` at `x` (`rerootAt`): the
edges on the path from the old root to `x` are reversed and every other
edge is kept, so the undirected represented tree is unchanged. Preferred
edges are reset (all dashed). On a vertex outside the forest this only
resets the preferred edges.

## Depends on

- [State](../part-03/state.md)

## Proof depends on

- [Tree](../../euler-tour-tree/part-01/tree.md)
- [Find Tree](../part-01/find-tree.md)
- [Remove Tree](../part-01/remove-tree.md)
- [Reroot At](../part-01/reroot-at.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.LinkCutTree](../../../../../../../../sources/v2/CSLibExt.md)
