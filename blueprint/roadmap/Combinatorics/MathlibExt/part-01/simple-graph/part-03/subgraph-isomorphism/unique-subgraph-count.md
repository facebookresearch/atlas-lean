---
article_id: af_55851d97e5253a9a8ddf5a44
declaration: def
origin: cited
statement: formalized
lean: SimpleGraph.uniqueSubgraphCount
---

# Unique Subgraph Count

For a finite vertex type, the number of distinct unique subgraphs of `H`: the number of
isomorphism classes of graphs
that occur exactly once as a subgraph of `H`. The set-builder ranges over spanning subgraphs
`G ≤ H` satisfying `IsUniqueSubgraph G H`; mapping each such `G` to its isomorphism class is a
bijection onto the once-occurring classes. In particular, automorphic copies do not inflate the
count: if distinct `G₁ ≤ H` and `G₂ ≤ H` are isomorphic, neither satisfies `IsUniqueSubgraph`
(the other is a second isomorphic copy), so neither is counted.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Is Unique Subgraph](is-unique-subgraph.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.SimpleGraph.SubgraphIsomorphism](../../../../../../../sources/v2/MathlibExt.md)
