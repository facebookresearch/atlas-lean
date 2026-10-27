---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.StronglyConnectedComponents.component_maximal
---

# Component maximal

Each returned block is the maximal mutual-reachability class of any one of its members.

## Depends on

- [Directed Adjacency](../directed-adjacency-2/part-01/directed-adjacency.md)
- [Strongly Connected](strongly-connected.md)
- [Components](components.md)

## Proof depends on

- [Decreasing Finish All](../depth-first-search/part-02/decreasing-finish-all.md)
- [Symm](symm.md)
- [Trans](trans.md)
- [Components pairwise disjoint](components-pairwise-disjoint.md)
- [Same Component B](same-component-b.md)
- [Same Component B eq true](same-component-b-eq-true.md)
- [Share component iff strongly Connected](share-component-iff-strongly-connected.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.StronglyConnectedComponents](../../../../../../sources/v2/CSLibExt.md)
