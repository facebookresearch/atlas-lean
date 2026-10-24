---
article_id: af_3be3d6372f9472cffc4ba118
declaration: theorem
origin: cited
lean: GaussBonnetBoundary.gauss_bonnet_with_boundary
---

# Theorem 41.3 (Gauss-Bonnet with boundary, for discs; proof sketched)

Let $M \subset \mathbb{R}^{3}$ be a surface, and $f \colon U \rightarrow M$ a partial parametrization, and $D \subset U$ a curvilinear disc. Take the simple closed curve $c$ which parametrizes the boundary of $D$, and consider the total geodesic curvature of $\gamma = f(c)$. This satisfies $\kappa_{\text{geod}}^{\text{tot}} = \int \kappa_{\text{geod}}(t)\, I_{c(t)}(c^{\prime}(t), c^{\prime}(t))^{1/2} \, dt = 2\pi - \int_{D} \kappa_{\text{gauss}} \sqrt{\operatorname{det} G} \, dx$ where $G$ is the first fundamental form.

## Depends on

- [Definition 12.1](../../part-01/chapter-2/040-definition-12-1.md)
- [Definition 12.3](../../part-01/chapter-2/042-definition-12-3.md)
- [Definition 14.4](../../part-01/chapter-2/049-definition-14-4.md)
- [Definition 29.3](../../part-01/lecture-29/090-definition-29-3.md)
- [Definition 41.1](144-definition-41-1.md)

## Sources

- [MIT 18.950 Differential Geometry (Fall 2008), Lecture 41](../../../../../sources/v1/DifferentialGeometry.md)
