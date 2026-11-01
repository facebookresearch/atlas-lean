---
article_id: af_1ed47cda28b30dc7ed4bf965
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.Kruskal.HasGreedyCutProperty
---

# Has Greedy Cut Property

At every ordered scan position whose edge joins distinct current components,
that edge has minimum stable key among all valid edges crossing the current
union-find partition.

## Depends on

- [Graph](../part-01/graph.md)

## Proof depends on

- [Key LE](../part-01/key-le.md)
- [State](../part-01/state.md)
- [Weighted Edge](../part-01/weighted-edge.md)
- [Key](../part-01/key.md)
- [Initial Forest](../part-01/initial-forest.md)
- [Ordered Edges](../part-01/ordered-edges.md)
- [Scan](scan.md)
- [Valid Edges](../part-01/valid-edges.md)
- [Equivalent](../../../data-structures/part-03/union-find/part-01/equivalent.md)
- [Forest](../../../data-structures/part-03/union-find/part-01/forest.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.Kruskal](../../../../../../../sources/v2/CSLibExt.md)
