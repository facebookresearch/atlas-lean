---
article_id: af_ecf4e792ba0ce9ba36490bee
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.LinkCutTree.State.mem_cut
---

# Mem cut

After `cut x`, the detached subtree occurs in the forest with root
`x`, so `x` itself remains a vertex, as does every vertex of its old tree
on the other side of the cut. The duplicate-free hypothesis is the
validity side condition under which pruning partitions the vertex set
(`mem_vertices_pruneAt_of_mem_not_mem`).

## Depends on

- [Tree](../../euler-tour-tree/part-01/tree.md)
- [Vertices](../../euler-tour-tree/part-01/vertices.md)
- [State](../part-03/state.md)
- [Mem](../part-03/mem.md)
- [Cut](cut.md)
- [Find Subtree](../part-01/find-subtree.md)
- [Find Tree](../part-01/find-tree.md)

## Proof depends on

- [Children ind](../../euler-tour-tree/part-01/children-ind.md)
- [Root](../../euler-tour-tree/part-01/root.md)
- [Vertices node](../../euler-tour-tree/part-01/vertices-node.md)
- [Mem vertices prune At of mem not mem](../part-02/mem-vertices-prune-at-of-mem-not-mem.md)
- [Prune At](../part-02/prune-at.md)
- [Remove Tree](../part-01/remove-tree.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.LinkCutTree](../../../../../../../../sources/v2/CSLibExt.md)
