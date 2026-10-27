---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.BreadthFirstSearch.predecessor_chain_unique
---

# Predecessor chain unique

Every reachable vertex has exactly one endpoint-inclusive saved-parent chain.

## Depends on

- [BFSForest](../internal/bfsforest.md)
- [Bfs With Parents](../internal/bfs-with-parents.md)
- [Directed Adjacency](../../../directed-adjacency-2/part-01/directed-adjacency.md)
- [Reachable](../../../directed-adjacency-2/part-01/reachable.md)

## Proof depends on

- [BFSResult](../../../breadth-first-search-2/bfsresult.md)
- [Bfs](../../../breadth-first-search-2/bfs.md)
- [Bfs With Parents ret](../../parents-2/bfs-with-parents-ret.md)
- [Distance present iff reachable](../../../breadth-first-search-2/distance-present-iff-reachable.md)
- [Edge](../../../directed-adjacency-2/part-01/edge.md)
- [Contents](../../../../data-structures/part-01/queue/semantics/contents.md)
- [Contents enqueue](../../../../data-structures/part-01/queue/semantics/contents-enqueue.md)
- [Contents eq cons of dequeue? eq some](../../../../data-structures/part-01/queue/semantics/contents-eq-cons-of-dequeue-eq-some.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.BreadthFirstSearch.Parents.Correctness](../../../../../../../../sources/v2/CSLibExt.md)
