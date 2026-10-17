---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.BreadthFirstSearch.BFSForest.pathTo?_spec
---

# Path To? spec

A returned path follows saved parents and graph edges, is simple and has minimal length.

## Depends on

- [BFSForest](../internal/bfsforest.md)
- [Path To?](../internal/path-to.md)
- [BFSResult](../../../breadth-first-search-2/bfsresult.md)
- [Bfs](../../../breadth-first-search-2/bfs.md)
- [Bfs With Parents](../internal/bfs-with-parents.md)
- [Directed Adjacency](../../../directed-adjacency-2/part-01/directed-adjacency.md)
- [Edge](../../../directed-adjacency-2/part-01/edge.md)

## Proof depends on

- [Path To? eq none iff](path-to-eq-none-iff.md)
- [Bfs With Parents ret](../../parents-2/bfs-with-parents-ret.md)
- [Distance eq some iff shortest](../../../breadth-first-search-2/distance-eq-some-iff-shortest.md)
- [Distance present iff reachable](../../../breadth-first-search-2/distance-present-iff-reachable.md)
- [Order mem iff reachable](../../../breadth-first-search-2/order-mem-iff-reachable.md)
- [Predecessor chain nodup](predecessor-chain-nodup.md)
- [Predecessor edge](../../parents-2/predecessor-edge.md)
- [Reachable](../../../directed-adjacency-2/part-01/reachable.md)
- [Walk](../../../directed-adjacency-2/part-01/walk.md)
- [Contents](../../../../data-structures/part-01/queue/semantics/contents.md)
- [Contents enqueue](../../../../data-structures/part-01/queue/semantics/contents-enqueue.md)
- [Contents eq cons of dequeue? eq some](../../../../data-structures/part-01/queue/semantics/contents-eq-cons-of-dequeue-eq-some.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.BreadthFirstSearch.Parents.Correctness](../../../../../../../../sources/v2/CSLibExt.md)
