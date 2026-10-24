---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.EdmondsKarp.edmondsKarp_minCut
---

# Edmonds Karp min Cut

The returned flow value equals the capacity of its residual-reachable cut.

## Depends on

- [Cut Capacity](cut-capacity.md)
- [Edmonds Karp](edmonds-karp.md)
- [Flow Value](../part-01/flow-value.md)
- [Residual Cut](residual-cut.md)

## Proof depends on

- [BFSResult](../../breadth-first-search-2/bfsresult.md)
- [Bfs](../../breadth-first-search-2/bfs.md)
- [Order mem iff reachable](../../breadth-first-search-2/order-mem-iff-reachable.md)
- [Edge](../../directed-adjacency-2/part-01/edge.md)
- [Reachable](../../directed-adjacency-2/part-01/reachable.md)
- [Flow](../part-01/flow.md)
- [Is Feasible](../part-01/is-feasible.md)
- [Edmonds Karp feasible](edmonds-karp-feasible.md)
- [Edmonds Karp no augmenting path](edmonds-karp-no-augmenting-path.md)
- [Residual Graph](../part-01/residual-graph.md)
- [Residual Graph edge iff](../part-01/residual-graph-edge-iff.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.EdmondsKarp](../../../../../../../sources/v2/CSLibExt.md)
