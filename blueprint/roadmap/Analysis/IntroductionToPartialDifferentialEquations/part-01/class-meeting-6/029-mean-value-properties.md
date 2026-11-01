---
article_id: af_4b41722de262e7d4e553c420
declaration: theorem
origin: cited
statement: formalized
lean: CM6.mean_value_property
---

# Theorem 4.1 (Mean value properties)

Let $u(x)$ be harmonic in the domain $\Omega \subset \mathbb{R}^{n}$, and let $B_{R}(x) \subset \Omega$ be a ball of radius $R$ centered at the point $x$. Then the following mean value formulas hold: $u(x)=\frac{n}{\omega_{n} R^{n}} \int_{B_{R}(x)} u(y) d^{n} y$ and $u(x)=\frac{1}{\omega_{n} R^{n-1}} \int_{\partial B_{R}(x)} u(\sigma) d \sigma$, where $\omega_{n}$ is the area of $\partial B_{1}(0) \subset \mathbb{R}^{n}$, that is, the area of the boundary of the unit ball in $\mathbb{R}^{n}$.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Theorem 7.1 (Divergence Theorem)](../class-meeting-1/011-divergence-theorem.md)

## Sources

- [MIT 18.152 Introduction to Partial Differential Equations (Fall 2011), Class Meeting #6, Section 4 (Mean value properties)](../../../../../sources/v1/IntroductionToPartialDifferentialEquations.md)
