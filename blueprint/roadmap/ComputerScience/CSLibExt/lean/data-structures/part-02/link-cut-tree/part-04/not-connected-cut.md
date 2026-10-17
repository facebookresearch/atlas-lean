---
article_id: af_9527bd5f91ee007afe7cf81a
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.LinkCutTree.State.not_connected_cut
---

# Not connected cut

A cut separates: after `cut x`, `x` is no longer connected to any
vertex of its old tree that lies outside the subtree rooted at `x`. No
invariant on the state is needed: `x` cannot occur in the pruned
remainder (`mem_vertices_pruneAt`).

## Depends on

- [Tree](../../euler-tour-tree/part-01/tree.md)
- [Vertices](../../euler-tour-tree/part-01/vertices.md)
- [State](../part-03/state.md)
- [Connected](../part-03/connected.md)
- [Cut](cut.md)
- [Find Subtree](../part-01/find-subtree.md)
- [Find Tree](../part-01/find-tree.md)

## Proof depends on

- [Children ind](../../euler-tour-tree/part-01/children-ind.md)
- [Root](../../euler-tour-tree/part-01/root.md)
- [Vertices node](../../euler-tour-tree/part-01/vertices-node.md)
- [Mem vertices prune At](../part-02/mem-vertices-prune-at.md)
- [Prune At](../part-02/prune-at.md)
- [Remove Tree](../part-01/remove-tree.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.LinkCutTree](../../../../../../../../sources/v2/CSLibExt.md)
