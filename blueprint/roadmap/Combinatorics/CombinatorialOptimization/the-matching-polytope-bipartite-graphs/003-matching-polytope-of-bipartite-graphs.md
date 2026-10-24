---
article_id: af_bf307580d6b26e287dbcb405
declaration: theorem
origin: cited
lean: BipartiteMatchingPolytope.bipartite_matching_polytope_eq
---

# Theorem 1 (matching polytope of bipartite graphs)

Let $G = (V, E)$ be a bipartite graph and let $M$ be the convex hull of the indicator vectors of all matchings of $G$. Define the relaxed polytope $P$ as the set of $x \in \mathbb{R}^E_{\geq 0}$ such that $\sum_{e \in \delta(v)} x_e \leq 1$ for all $v \in V$. Then $P = M$, i.e.\ every vertex of $P$ is the indicator vector of a matching.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Claim 1 (matching characterization)](../polyhedral-combinatorics/001-matching-characterization.md)
- [Observation 2 (integrality of vertex solutions)](004-integrality-of-vertex-solutions.md)
- [Definition 3 (totally unimodular matrix)](005-totally-unimodular-matrix.md)
- [Lemma 4 (constraint matrix is totally unimodular)](006-constraint-matrix-is-totally-unimodular.md)

## Sources

- [MIT 18.433 Combinatorial Optimization (Fall 2003), The Matching Polytope - Bipartite Graphs, Sept 18](../../../../sources/v1/CombinatorialOptimization.md)
