---
article_id: af_dcb590716b7d1e173e34e9e3
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: TopCat.Presheaf.isSheaf_iff_gluing_and_locality
---

# Definition 22

A presheaf $\mathcal{F}$ on the topological space $X$ is called a sheaf if the following is true for any (possibly infinite) open covering of an open subset $U = \bigcup U_\alpha$: 1.\ for a collection of sections $(s_\alpha) \in \prod_\alpha \mathcal{F}(U_\alpha)$, if they coincide on intersections, that is $s_\alpha|_{U_\beta} = s_\beta|_{U_\alpha}$, then there exists a section $s$ on $U$ such that $s|_{U_\alpha} = s_\alpha$; 2.\ the map $\prod_\alpha \varphi_{U_\alpha}^U$ is injective.

## Depends on

- [Definition 21](084-definition-21.md)

## Sources

- [MIT 18.725 Algebraic Geometry (Fall 2015), Lecture 10](../../../../../sources/v1/AlgebraicGeometryI.md)
