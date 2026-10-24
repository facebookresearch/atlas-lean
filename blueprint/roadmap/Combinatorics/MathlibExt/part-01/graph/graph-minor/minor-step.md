---
article_id: af_2bb4798bbf109b23da3bf8b2
declaration: inductive
origin: cited
statement: formalized
lean: MetaMathlibExt.MinorStep
---

# Minor Step

Single-step minor operation: `iso` is relabelling up to graph isomorphism;
`deleteVertex` is deletion of exactly one vertex (induced subgraph missing the
image of one vertex); `deleteEdge` is deletion of exactly one edge (vertices
identified up to an equivalence, edge sets agree except for one distinguished
edge); `contractEdge` collapses exactly one adjacent pair (a surjective map
identifying a single adjacent pair `a, b` and injective otherwise, with
adjacency in `H` given by images of adjacent pairs in `G` at distinct vertices,
so no loop is forced at the identified vertex).
Stable source: https://en.wikipedia.org/wiki/Robertson%E2%80%93Seymour_theorem.

## Depends on

- [Fin Graph](fin-graph.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Graph.GraphMinor](../../../../../../sources/v2/MathlibExt.md)
