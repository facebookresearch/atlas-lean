---
article_id: af_9ab77b095cdd549c11c79ab8
declaration: theorem
origin: cited
lean: SchrodingerEquation.theorem_2_1_nD
---

# Theorem 2.1 (The Solution to the Global Cauchy Problem Schrödinger's Equation and the Dispersive Estimate)

Let $\phi(x) \in C_{c}^{\infty}(\mathbb{R}^{n})$. Then there exists a unique solution $\psi \in C^{\infty}((0, \infty) \times \mathbb{R}^{n})$ to the free Schrödinger equation $$i \partial_{t} \psi(t, x)+\frac{1}{2} \Delta \psi(t, x) =0, \quad t>0, x \in \mathbb{R}^{n},$$ $$\psi(0, x) =\phi(x), \quad x \in \mathbb{R}^{n}.$$ The solution can be expressed as $$\psi(t, x)=[K(t, \cdot) * \phi(\cdot)](x),$$ where $K(t, x)$ is the fundamental solution . Furthermore, for each $t>0$, the solution $\psi(t, x)$ verifies the dispersive estimate $$\|\psi(t, \cdot)\|_{C_{0}} \coloneqq \max_{x \in \mathbb{R}^{n}}|\psi(t, x)| \leq \frac{C}{t^{n / 2}}\|\phi\|_{L^{1}} \coloneqq \frac{C}{t^{n / 2}} \int|\phi(x)| d^{n} x.$$ Above, $C>0$ is a constant that does not depend on the initial data.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Proposition 2.0.3 (The behavior of $K(t, \cdot) * \phi(\cdot)$ as $t \downarrow 0$)](085-t-cdot.md)

## Sources

- [MIT 18.152 Introduction to Partial Differential Equations (Fall 2011), Class Meeting on Schrödinger's equation, Section 2](../../../../../sources/v1/IntroductionToPartialDifferentialEquations.md)
