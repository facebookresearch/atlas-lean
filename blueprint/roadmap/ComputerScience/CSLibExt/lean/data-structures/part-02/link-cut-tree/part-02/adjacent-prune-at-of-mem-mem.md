---
article_id: af_5717ec048456af7490338190
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.LinkCutTree.adjacent_pruneAt_of_mem_mem
---

# Adjacent prune At of mem mem

Pruning keeps every edge whose endpoints survive: in a duplicate-free
tree, an edge of the original tree with both endpoints in the pruned
remainder is an edge of the remainder. Together with
`mem_vertices_pruneAt` (which gives the converse inclusion of vertices)
this specifies `pruneAt` at edge level on the surviving vertices.

## Depends on

- [Tree](../../euler-tour-tree/part-01/tree.md)
- [Vertices](../../euler-tour-tree/part-01/vertices.md)
- [Adjacent](../part-01/adjacent.md)
- [Prune At](prune-at.md)

## Proof depends on

- [Children ind](../../euler-tour-tree/part-01/children-ind.md)
- [Root](../../euler-tour-tree/part-01/root.md)
- [Vertices node](../../euler-tour-tree/part-01/vertices-node.md)
- [Mem left](../part-01/mem-left.md)
- [Mem right](../part-01/mem-right.md)
- [Mem vertices prune At](mem-vertices-prune-at.md)
- [Root prune At](root-prune-at.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.LinkCutTree](../../../../../../../../sources/v2/CSLibExt.md)
