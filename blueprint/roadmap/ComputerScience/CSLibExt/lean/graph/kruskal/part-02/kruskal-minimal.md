---
article_id: af_152c7fab9901e2db635a09ef
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.Kruskal.kruskal_minimal
---

# Kruskal minimal

With natural-number weights, Kruskal has minimum total weight among all canonical
spanning forests, including disconnected graphs and parallel input occurrences.
This is the cut-exchange argument of CLRS, fourth edition, §21.2.

## Depends on

- [Graph](../part-01/graph.md)
- [Is Spanning Forest](../part-01/is-spanning-forest.md)
- [Weighted Edge](../part-01/weighted-edge.md)
- [Kruskal](kruskal.md)
- [Total Weight](../part-01/total-weight.md)

## Proof depends on

- [Acyclic](../part-01/acyclic.md)
- [Acyclic Rev](../part-01/acyclic-rev.md)
- [Connected](../part-01/connected.md)
- [Connected Rev](../part-01/connected-rev.md)
- [Key LE](../part-01/key-le.md)
- [Spans](../part-01/spans.md)
- [State](../part-01/state.md)
- [Step](step.md)
- [Key](../part-01/key.md)
- [Initial Forest](../part-01/initial-forest.md)
- [Kruskal is Spanning Forest](kruskal-is-spanning-forest.md)
- [Kruskal light edge](kruskal-light-edge.md)
- [Ordered Edges](../part-01/ordered-edges.md)
- [Scan](scan.md)
- [Sort Edges](../part-01/sort-edges.md)
- [Valid Edges](../part-01/valid-edges.md)
- [Equivalent](../../../data-structures/part-03/union-find/part-01/equivalent.md)
- [Forest](../../../data-structures/part-03/union-find/part-01/forest.md)
- [Equivalent union iff](../../../data-structures/part-03/union-find/part-01/equivalent-union-iff.md)
- [Find](../../../data-structures/part-03/union-find/part-01/find.md)
- [Union](../../../data-structures/part-03/union-find/part-01/union.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.Kruskal](../../../../../../../sources/v2/CSLibExt.md)
