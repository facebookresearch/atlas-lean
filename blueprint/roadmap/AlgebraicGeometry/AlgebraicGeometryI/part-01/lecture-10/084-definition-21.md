---
article_id: af_9ed0943f3db3b49893ee35f4
declaration: def
origin: cited
lean: presheaf_def
---

# Definition 21

A presheaf of sets $\mathcal{F}$ on the topological space $X$ is an assignment for an open subset $U \subset X$ of a set $\mathcal{F}(U)$ and for a pair of open subsets $V \subset U \subset X$ of a so called restriction map $\varphi_V^U \colon \mathcal{F}(U) \to \mathcal{F}(V)$ such that the following axioms hold: 1.\ for each triple of open subsets $W \subset V \subset U \subset X$ the composition of the restriction maps $\varphi_W^V \circ \varphi_V^U$ is equal to the restriction $\varphi_W^U$; 2.\ for each open subset $U \subset X$, the restriction $\varphi_U^U$ is equal to the identity map. Elements of the sets $\mathcal{F}(U)$ are called sections of the presheaf $\mathcal{F}$ over the open subset $U$.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.725 Algebraic Geometry (Fall 2015), Lecture 10: Sheaves, Invertible Sheaves on P^1](../../../../../sources/v1/AlgebraicGeometryI.md)
