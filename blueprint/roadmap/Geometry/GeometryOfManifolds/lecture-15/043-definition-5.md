---
article_id: af_a6bed684c6db39d4ec222314
declaration: structure
origin: cited
lean: IsEllipticOperatorOnManifold
---

# Definition 5 (Lecture 15, Section 1, Hodge Theory)

A differential operator of order $k$ is a linear map $L \colon \Gamma(E) \rightarrow \Gamma(F)$ such that, locally in coordinates, $L(s) = \sum_{|\alpha| \leq k} A_{\alpha} \frac{\partial^{|\alpha|} s}{\partial x^{\alpha}}$ where each $A_{\alpha}$ is a $C^{\infty}$ function with values in matrices, i.e.\ a local section of $\operatorname{Hom}(E, F)$. The symbol of $L$ is the map $\sigma_{k} \colon T_{x}^{*}M \ni \xi \mapsto \sum_{|\alpha|=k} A_{\alpha}(x)\, \xi_{1}^{\alpha_{1}} \cdots \xi_{n}^{\alpha_{n}} \in \operatorname{Hom}(E_{x}, F_{x})$. $L$ is elliptic if for every nonzero $\xi$, $\sigma(\xi)$ is an isomorphism.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.966 Geometry of Manifolds (Spring 2007), Lecture 15, Section 1, Hodge Theory](../../../../sources/v1/GeometryOfManifolds.md)
