---
article_id: af_48e817deab4c7d1f297bde9c
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.LinkCutTree.State.link
---

# Link

Link the represented trees of `x` and `y` with the new edge `x`-`y`,
as in the textbook operation: the tree of `x` is first rerooted at `x`
(`rerootAt`, so `x` becomes its root with every old edge kept) and then
grafted as a new child subtree of `y` (`graftAt`), adding exactly the edge
from `y` to `x`. Linking two vertices of the same tree, or a vertex
outside the forest, leaves the forest unchanged. Preferred edges are
reset.

## Depends on

- [State](../part-03/state.md)

## Proof depends on

- [Tree](../../euler-tour-tree/part-01/tree.md)
- [Vertices](../../euler-tour-tree/part-01/vertices.md)
- [Find Tree](../part-01/find-tree.md)
- [Graft At](../part-01/graft-at.md)
- [Remove Tree](../part-01/remove-tree.md)
- [Reroot At](../part-01/reroot-at.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.LinkCutTree](../../../../../../../../sources/v2/CSLibExt.md)
