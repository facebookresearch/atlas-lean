---
article_id: af_0bb93d9829e959b0d02c98ae
declaration: theorem
origin: cited
statement: formalized
lean: CM14.energy_estimate_cone
---

# Theorem 2.1 (Energy estimates in a cone)

Let $\phi(t,x)$ be a $C^{2}$ solution to the $1+n$ dimensional global Cauchy problem for the linear wave equation $\square_{m} \phi=0$, $\phi(0,x)=f(x)$, $\partial_{t} \phi(0,x)=g(x)$, $x \in \mathbb{R}^{n}$. Let $R \in [0,\infty]$, let $X$ be the past-directed timelike vector defined by $X^{\mu}=-\delta_{0}^{\mu}$, and let ${}^{(X)} J^{\mu}[\phi(t,y)]$ be the compatible current associated to $X$. Define the square of the energy $E[\phi](t)$ by $E^{2}[\phi](t) \coloneqq \int_{B_{R-t}(p)} \hat{N}_{\mu} {}^{(X)} J^{\mu}[\phi(t,y)] d^{n} y = \frac{1}{2} \int_{B_{R-t}(p)} |\nabla_{t,y} \phi(t,y)|^{2} d^{n} y$ where $\hat{N}_{\mu}=\delta_{\mu}^{0}$ is the past-pointing unit normal covector to $\{t\} \times B_{R-t}(p) \subset \mathbb{R}^{4}$, and $B_{R}(p) \subset \mathbb{R}^{3}$ denotes the solid Euclidean ball of radius $R$ centered at $p$. Then $E[\phi](t) \leq E[\phi](0)$.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Definition 1.0.2 (Class Meeting #13, Section 1)](058-definition-1-0-2.md)
- [Corollary 1.0.3](059-corollary-1-0-3.md)
- [Lemma 1.0.1 (Dominant Energy Condition for $T_{\mu \nu}$)](056-dominant-energy-condition-for-t-mu-nu.md)
- [Definition 1.0.1 (Class Meeting #13, Section 1)](055-definition-1-0-1.md)
- [Theorem 1.1 (Divergence Theorem)](060-divergence-theorem.md)

## Sources

- [MIT 18.152 Introduction to Partial Differential Equations (Fall 2011), Class Meeting #13, Section 2](../../../../../sources/v1/IntroductionToPartialDifferentialEquations.md)
