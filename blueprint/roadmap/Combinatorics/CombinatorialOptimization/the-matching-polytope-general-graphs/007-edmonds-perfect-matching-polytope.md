---
article_id: af_b5b4c6740adfc60a0eaaee8e
declaration: theorem
origin: cited
lean: SimpleGraph.edmonds_perfect_matching_polytope
---

# Theorem 1 (Edmonds, perfect matching polytope)

Let $G = (V, E)$ be any graph (not necessarily bipartite) with $|V|$ even, and let $\operatorname{PM}(G)$ be the convex hull of indicator vectors of perfect matchings of $G$. Define $P$ to be the set of $x \in \mathbb{R}^E$ satisfying (1) $x_e \geq 0$ for all $e \in E$, (2) $\sum_{e \in \delta(v)} x_e = 1$ for all $v \in V$, and (3) $\sum_{e \in \delta(S)} x_e \geq 1$ for every odd-sized subset $S$ of $V$. Then $P = \operatorname{PM}(G)$.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Claim 2 (decomposition into perfect matchings)](008-decomposition-into-perfect-matchings.md)

## Sources

- [MIT 18.433 Combinatorial Optimization (Fall 2003), The Matching Polytope - General graphs, Sept 23](../../../../sources/v1/CombinatorialOptimization.md)
