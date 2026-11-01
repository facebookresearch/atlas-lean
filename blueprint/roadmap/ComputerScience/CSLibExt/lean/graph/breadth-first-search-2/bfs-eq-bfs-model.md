---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.BreadthFirstSearch.bfs_eq_bfsModel
---

# Bfs eq bfs Model

The expected-linear-time executable BFS refines the kernel-reducible list model.

## Depends on

- [BFSResult](bfsresult.md)
- [Bfs](bfs.md)
- [Bfs Model](bfs-model.md)
- [Directed Adjacency](../directed-adjacency-2/part-01/directed-adjacency.md)

## Proof depends on

- [Edge](../directed-adjacency-2/part-01/edge.md)
- [Walk](../directed-adjacency-2/part-01/walk.md)
- [Contents](../../data-structures/part-01/queue/semantics/contents.md)
- [Contents enqueue](../../data-structures/part-01/queue/semantics/contents-enqueue.md)
- [Contents eq cons of dequeue? eq some](../../data-structures/part-01/queue/semantics/contents-eq-cons-of-dequeue-eq-some.md)
- [Dequeue? eq none iff](../../data-structures/part-01/queue/semantics/dequeue-eq-none-iff.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.BreadthFirstSearch](../../../../../../sources/v2/CSLibExt.md)
