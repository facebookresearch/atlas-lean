---
article_id: af_3ae112e31f441333c0ae9167
declaration: def
origin: cited
statement: formalized
lean: SimpleGraph.EdgeIndexedMultigraph.maxDegree
---

# Max Degree

The maximum degree of a finite edge-indexed multigraph. Requires finite edge
identities: `M.degree` counts via `Set.ncard`, which collapses infinite
incident sets, so without `[Finite E]` this could report `0` for a genuinely
infinite-degree multigraph.

## Depends on

- [Edge Indexed Multigraph](../part-01/edge-indexed-multigraph.md)

## Proof depends on

- [Degree](degree.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.SimpleGraph.EdgeIndexedMultigraph](../../../../../../../../sources/v2/MathlibExt.md)
