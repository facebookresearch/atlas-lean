---
article_id: af_4572312339594e5af562506f
declaration: theorem
origin: cited
statement: formalized
lean: SimpleGraph.edmonds_progress
---

# Lemma 9 (progress lemma for Edmonds' algorithm)

At each step of Edmonds' blossom algorithm for matching in a general graph, exactly one of the following occurs: the alternating forest $F$ is extended; the underlying graph $G$ is reduced by a blossom contraction; an augmenting path is found; or the algorithm terminates with a maximum matching.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Lemma 2 (Berge, max matching iff no augmenting path)](022-berge-max-matching-iff-no-augmenting-pat.md)
- [Lemma 8 (Cycle Shrinking / Edmonds)](028-cycle-shrinking-edmonds.md)

## Sources

- [MIT 18.433 Combinatorial Optimization (Fall 2003), Matching Algorithms, Sept 4-9-11 (General graphs)](../../../../sources/v1/CombinatorialOptimization.md)
