---
article_id: af_f47946eb4c69cb69cb3d93c5
declaration: theorem
origin: cited
lean: GraphContainers.graph_container_fingerprints
---

# Theorem 11.2.3 (Graph container theorem, with fingerprints)

For every $c > 0$, there exists $\delta > 0$ such that the following holds. Let $G = (V, E)$ be a graph with average degree $d$ and maximum degree at most $cd$. Writing $\mathcal{I}$ for the collection of independent sets of $G$, there exist functions $S \colon \mathcal{I} \to 2^V$ and $A \colon 2^V \to 2^V$ (one only needs to define $A(\cdot)$ on sets in the image of $S$) such that, for every $I \in \mathcal{I}$, (1) $S(I) \subseteq I \subseteq S(I) \cup A(S(I))$, (2) $|S(I)| \leq 2\delta |V|/d$, (3) $|S(I) \cup A(S(I))| \leq (1 - \delta)|V|$.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.226 Probabilistic Methods in Combinatorics (Fall 2022), Chapter 11, Section 11.2](../../../../sources/v1/ProbabilisticMethodsInCombinatorics.md)
