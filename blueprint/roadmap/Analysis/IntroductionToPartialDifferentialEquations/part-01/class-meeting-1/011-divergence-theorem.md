---
article_id: af_18d52e087c3871175a9a575f
declaration: theorem
origin: cited
lean: VectorCalculus.divergence_theorem
---

# Theorem 7.1 (Divergence Theorem)

Let $\Omega \subset \mathbb{R}^{3}$ be a domain with a boundary that we denote by $\partial \Omega$. Then the following formula holds: $\int_{\Omega} \nabla \cdot \mathbf{F}(x, y, z) \, dx \, dy \, dz=\int_{\partial \Omega} \mathbf{F}(\sigma) \cdot \hat{\mathbf{N}}(\sigma) \, d \sigma$. Above, $\hat{\mathbf{N}}(\sigma)$ is the unit outward normal vector to $\partial \Omega$, and $d \sigma$ is the surface measure induced on $\partial \Omega$.

## Depends on

- [Definition 7.2.2 (Divergence)](010-divergence.md)
- [Definition 7.2.1 (Vectorfield)](009-vectorfield.md)

## Sources

- [MIT 18.152 Introduction to Partial Differential Equations (Fall 2011), Class Meeting #1, Section 7.2](../../../../../sources/v1/IntroductionToPartialDifferentialEquations.md)
