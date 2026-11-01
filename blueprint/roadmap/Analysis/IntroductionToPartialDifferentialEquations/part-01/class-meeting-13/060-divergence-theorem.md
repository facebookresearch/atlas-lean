---
article_id: af_67c59f878783654dc985f73d
declaration: theorem
origin: cited
statement: formalized
lean: CM14.spacetime_divergence_theorem
---

# Theorem 1.1 (Divergence Theorem)

Let $\phi$ be a solution to the linear wave equation $\square_{m} \phi=0$. Let $X$ be any vectorfield, and let ${}^{(X)} J$ be the compatible current defined in Definition 1.0.2. Let $\Omega \subset \mathbb{R}^{1+n}$ be a domain with boundary $\partial \Omega$. Then the following integral identity holds: $\int_{\partial \Omega} \hat{N}_{\alpha} {}^{(X)} J^{\alpha}[\phi(\sigma)] d\sigma = \int_{\Omega} \partial_{\mu}({}^{(X)} J^{\mu}[\phi(t,x)]) dt\, d^{n} x$.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Definition 1.0.2 (Class Meeting #13, Section 1)](058-definition-1-0-2.md)

## Sources

- [MIT 18.152 Introduction to Partial Differential Equations (Fall 2011), Class Meeting #13, Section 1](../../../../../sources/v1/IntroductionToPartialDifferentialEquations.md)
