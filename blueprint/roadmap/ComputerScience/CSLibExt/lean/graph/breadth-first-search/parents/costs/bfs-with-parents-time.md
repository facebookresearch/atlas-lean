---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.BreadthFirstSearch.bfsWithParents_time
---

# Bfs With Parents time

Exact selected BFS events: attempts, adjacency checks, enqueues and parent writes.

## Depends on

- [BFSForest](../internal/bfsforest.md)
- [BFSResult](../../../breadth-first-search-2/bfsresult.md)
- [Bfs](../../../breadth-first-search-2/bfs.md)
- [Bfs With Parents](../internal/bfs-with-parents.md)
- [Directed Adjacency](../../../directed-adjacency-2/part-01/directed-adjacency.md)

## Proof depends on

- [Bfs With Parents ret](../../parents-2/bfs-with-parents-ret.md)
- [Edge](../../../directed-adjacency-2/part-01/edge.md)
- [Contents](../../../../data-structures/part-01/queue/semantics/contents.md)
- [Contents enqueue](../../../../data-structures/part-01/queue/semantics/contents-enqueue.md)
- [Contents eq cons of dequeue? eq some](../../../../data-structures/part-01/queue/semantics/contents-eq-cons-of-dequeue-eq-some.md)
- [Dequeue? eq none iff](../../../../data-structures/part-01/queue/semantics/dequeue-eq-none-iff.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.BreadthFirstSearch.Parents.Costs](../../../../../../../../sources/v2/CSLibExt.md)
