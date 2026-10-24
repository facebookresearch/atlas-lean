---
article_id: af_b097775dc77d625cc561d346
declaration: theorem
origin: cited
lean: SimpleGraph.blossom_shrinking
---

# Lemma 8 (Cycle Shrinking / Edmonds)

Let $M$ be a matching of an undirected graph $G$ and let $B$ be a blossom (an odd-length cycle of length $2k+1$ containing exactly $k$ edges of $M$) which is vertex-disjoint from $M$ outside of $B$. Let $G'$ be the graph obtained from $G$ by contracting $B$ to a single vertex, and let $M'$ be the matching of $G'$ induced by $M$. Then $M'$ is a maximum matching of $G'$ if and only if $M$ is a maximum matching of $G$.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Lemma 2 (Berge, max matching iff no augmenting path)](022-berge-max-matching-iff-no-augmenting-pat.md)

## Sources

- [MIT 18.433 Combinatorial Optimization (Fall 2003), Matching Algorithms, Sept 4-9-11 (General graphs)](../../../../sources/v1/CombinatorialOptimization.md)
