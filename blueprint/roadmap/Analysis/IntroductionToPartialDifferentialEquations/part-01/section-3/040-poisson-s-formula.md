---
article_id: af_71fc352e303229383558333e
declaration: theorem
origin: cited
lean: PoissonHarnack.poisson_formula
---

# Theorem 3.1 (Poisson's formula)

Let $B_{R}(p) \subset \mathbb{R}^{3}$ be a ball of radius $R$ centered at $p=(p^{1}, p^{2}, p^{3})$, and let $x=(x^{1}, x^{2}, x^{3})$ denote a point in $\mathbb{R}^{3}$. Then the unique solution $u \in C^{2}(B_{R}(p)) \cap C(\bar{B}_{R}(p))$ of the PDE $\Delta u=0$, $x \in \Omega$, $u(x)=f(x)$, $x \in \partial \Omega$, can be represented using the Poisson formula: $u(x)=\frac{R^{2}-|x-p|^{2}}{4\pi R} \int_{\partial B_{R}(p)} \frac{f(\sigma)}{|x-\sigma|^{3}} d \sigma$.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Theorem 2.2 (Representation formula for solutions to the boundary value Poisson equation)](../section-2/039-representation-formula-for-solutions-to.md)
- [Lemma 2.0.1](../class-meeting-9/043-lemma-2-0-1.md)

## Sources

- [MIT 18.152 Introduction to Partial Differential Equations (Fall 2011), Section 3](../../../../../sources/v1/IntroductionToPartialDifferentialEquations.md)
