---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.BreadthFirstSearch.BFSForest.pathTo?_time_of_not_reachable
---

# Path To? time of not reachable

An unreachable target incurs one source comparison and one missing parent lookup.

## Depends on

- [BFSForest](../internal/bfsforest.md)
- [Path To?](../internal/path-to.md)
- [Bfs With Parents](../internal/bfs-with-parents.md)
- [Directed Adjacency](../../../directed-adjacency-2/part-01/directed-adjacency.md)
- [Reachable](../../../directed-adjacency-2/part-01/reachable.md)

## Proof depends on

- [BFSResult](../../../breadth-first-search-2/bfsresult.md)
- [Bfs](../../../breadth-first-search-2/bfs.md)
- [Bfs With Parents ret](../../parents-2/bfs-with-parents-ret.md)
- [Order mem iff reachable](../../../breadth-first-search-2/order-mem-iff-reachable.md)
- [Predecessor eq none iff](../../parents-2/predecessor-eq-none-iff.md)
- [Edge](../../../directed-adjacency-2/part-01/edge.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.BreadthFirstSearch.Parents.Correctness](../../../../../../../../sources/v2/CSLibExt.md)
