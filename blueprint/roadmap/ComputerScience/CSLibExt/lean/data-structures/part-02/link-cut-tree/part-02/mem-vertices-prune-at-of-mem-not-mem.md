---
article_id: af_d2db6d6000492cf6ea3d6e4a
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.LinkCutTree.mem_vertices_pruneAt_of_mem_not_mem
---

# Mem vertices prune At of mem not mem

The vertices on the other side of a prune survive: in a duplicate-free
(valid) tree, every vertex outside the detached subtree at `x` is a vertex
of the pruned remainder. Together with `mem_vertices_pruneAt` this says
pruning partitions the vertex set of a valid tree into the detached
subtree and the remainder, keeping all remaining edges.

## Depends on

- [Tree](../../euler-tour-tree/part-01/tree.md)
- [Vertices](../../euler-tour-tree/part-01/vertices.md)
- [Find Subtree](../part-01/find-subtree.md)
- [Prune At](prune-at.md)

## Proof depends on

- [Children ind](../../euler-tour-tree/part-01/children-ind.md)
- [Root](../../euler-tour-tree/part-01/root.md)
- [Vertices node](../../euler-tour-tree/part-01/vertices-node.md)
- [Prune At eq self of not mem](prune-at-eq-self-of-not-mem.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.LinkCutTree](../../../../../../../../sources/v2/CSLibExt.md)
