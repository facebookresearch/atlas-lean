---
article_id: af_d011e8f3bcc8953de519695d
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.LinkCutTree.State.not_connected_cutEdge
---

# Not connected cut Edge

An edge cut separates its endpoints: in a valid state, after
`cutEdge x y` on an adjacent pair, `x` and `y` lie in different
represented trees. Rerooting at `x` keeps the edge (`adjacent_rerootAt`)
and makes the subtree at `y` root-free of `x`, so the rooted separation
theorem `not_connected_cut` applies.

## Depends on

- [Tree](../../euler-tour-tree/part-01/tree.md)
- [Adjacent](../part-01/adjacent.md)
- [State](../part-03/state.md)
- [Connected](../part-03/connected.md)
- [Valid](../part-03/valid.md)
- [Cut Edge](../part-04/cut-edge.md)

## Proof depends on

- [Children ind](../../euler-tour-tree/part-01/children-ind.md)
- [Root](../../euler-tour-tree/part-01/root.md)
- [Vertices](../../euler-tour-tree/part-01/vertices.md)
- [Vertices node](../../euler-tour-tree/part-01/vertices-node.md)
- [Mem left](../part-01/mem-left.md)
- [Mem right](../part-01/mem-right.md)
- [Parent Child](../part-02/parent-child.md)
- [Mem](../part-03/mem.md)
- [Make Root](../part-04/make-root-2.md)
- [Cut](../part-04/cut.md)
- [Cut Edge eq cut make Root of adjacent](../part-04/cut-edge-eq-cut-make-root-of-adjacent.md)
- [Make Root](../part-04/make-root.md)
- [Not connected cut](../part-04/not-connected-cut.md)
- [Adjacent reroot At](../part-01/adjacent-reroot-at.md)
- [Find Subtree](../part-01/find-subtree.md)
- [Find Tree](../part-01/find-tree.md)
- [Graft At](../part-01/graft-at.md)
- [Mem vertices graft At](../part-01/mem-vertices-graft-at.md)
- [Mem vertices reroot At](../part-01/mem-vertices-reroot-at.md)
- [Perm vertices reroot At](../part-02/perm-vertices-reroot-at.md)
- [Remove Tree](../part-01/remove-tree.md)
- [Reroot At](../part-01/reroot-at.md)
- [Reroot At eq none of not mem](../part-01/reroot-at-eq-none-of-not-mem.md)
- [Root graft At](../part-01/root-graft-at.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.LinkCutTree](../../../../../../../../sources/v2/CSLibExt.md)
