---
article_id: af_6515203632d853d2792d1ff5
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.LinkCutTree.State.adjacent_cutEdge
---

# Adjacent cut Edge

An edge cut retains every other edge: in a valid state, after
`cutEdge x y` on an adjacent pair, every represented edge other than
`x`-`y` itself is still an edge of some represented tree. Edges of other
trees pass through untouched; edges of the cut tree survive the
rerooting (`adjacent_rerootAt`) and then lie on one side of the prune,
where they are kept by `adjacent_pruneAt_of_mem_mem` (remainder side) or
`adjacent_findSubtree_of_mem_mem` (detached side); the only edge
crossing the prune is `x`-`y` (`adjacent_node_crossing`).

## Depends on

- [Tree](../../euler-tour-tree/part-01/tree.md)
- [Adjacent](../part-01/adjacent.md)
- [State](../part-03/state.md)
- [Valid](../part-03/valid.md)
- [Cut Edge](../part-04/cut-edge.md)

## Proof depends on

- [Children ind](../../euler-tour-tree/part-01/children-ind.md)
- [Root](../../euler-tour-tree/part-01/root.md)
- [Vertices](../../euler-tour-tree/part-01/vertices.md)
- [Vertices node](../../euler-tour-tree/part-01/vertices-node.md)
- [Mem left](../part-01/mem-left.md)
- [Mem right](../part-01/mem-right.md)
- [Symm](../part-01/symm.md)
- [Parent Child](../part-02/parent-child.md)
- [Mem](../part-03/mem.md)
- [Make Root](../part-04/make-root-2.md)
- [Cut](../part-04/cut.md)
- [Cut Edge eq cut make Root of adjacent](../part-04/cut-edge-eq-cut-make-root-of-adjacent.md)
- [Make Root](../part-04/make-root.md)
- [Adjacent prune At of mem mem](../part-02/adjacent-prune-at-of-mem-mem.md)
- [Adjacent reroot At](../part-01/adjacent-reroot-at.md)
- [Find Subtree](../part-01/find-subtree.md)
- [Find Tree](../part-01/find-tree.md)
- [Graft At](../part-01/graft-at.md)
- [Mem vertices graft At](../part-01/mem-vertices-graft-at.md)
- [Mem vertices reroot At](../part-01/mem-vertices-reroot-at.md)
- [Perm vertices prune At](../part-02/perm-vertices-prune-at.md)
- [Perm vertices reroot At](../part-02/perm-vertices-reroot-at.md)
- [Prune At](../part-02/prune-at.md)
- [Remove Tree](../part-01/remove-tree.md)
- [Reroot At](../part-01/reroot-at.md)
- [Reroot At eq none of not mem](../part-01/reroot-at-eq-none-of-not-mem.md)
- [Root graft At](../part-01/root-graft-at.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.LinkCutTree](../../../../../../../../sources/v2/CSLibExt.md)
