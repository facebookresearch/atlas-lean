---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.StronglyConnectedComponents.components_condensationAcyclic
---

# Components condensation Acyclic

Mutual reachability between returned components forces them to be equal;
equivalently, the condensation relation has no nontrivial directed cycle.

## Depends on

- [Directed Adjacency](../directed-adjacency-2/part-01/directed-adjacency.md)
- [Condensation Acyclic](condensation-acyclic.md)
- [Components](components.md)

## Proof depends on

- [Decreasing Finish All](../depth-first-search/part-02/decreasing-finish-all.md)
- [Edge](../directed-adjacency-2/part-01/edge.md)
- [Reachable](../directed-adjacency-2/part-01/reachable.md)
- [Component Reaches](component-reaches.md)
- [Strongly Connected](strongly-connected.md)
- [Symm](symm.md)
- [Trans](trans.md)
- [Component maximal](component-maximal.md)
- [Components pairwise disjoint](components-pairwise-disjoint.md)
- [Same Component B](same-component-b.md)
- [Same Component B eq true](same-component-b-eq-true.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.StronglyConnectedComponents](../../../../../../sources/v2/CSLibExt.md)
