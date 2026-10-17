---
article_id: af_13eb240609b57c1d79b3f7a4
declaration: theorem
origin: cited
statement: formalized
lean: SimpleGraph.forest_characterization
---

# Lemma 3 (forest characterization of maximum matching)

Let $G$ be a bipartite graph with vertex partition $(A, B)$, let $M$ be a matching of $G$, and let $A^U$ and $B^U$ be the vertices of $A$ and $B$ unmatched by $M$. Build the alternating forest $F$ starting from the unmatched vertices $A^U$ as in Section 1. Then $M$ is a maximum matching if and only if no vertex of $B^U$ lies in $F$.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Lemma 2 (Berge, max matching iff no augmenting path)](022-berge-max-matching-iff-no-augmenting-pat.md)

## Sources

- [MIT 18.433 Combinatorial Optimization (Fall 2003), Matching Algorithms, Sept 4-9-11 (Bipartite graphs)](../../../../sources/v1/CombinatorialOptimization.md)
