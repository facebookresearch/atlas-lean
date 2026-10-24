---
article_id: af_800b779fabcbf787291db182
declaration: theorem
origin: cited
statement: formalized
lean: Duhamel.theorem_1_2_duhamel
---

# Theorem 1.2 (Duhamel's principle)

Let $g(x)$ and $T \coloneqq \frac{1}{4 D b}$ be as in Theorem 1.1. Also assume that $f(t, x)$, $\partial_{i} f(t, x)$, and $\partial_{i} \partial_{j} f(t, x)$ are continuous, bounded functions on $[0, T) \times \overline{\mathbb{R}^{n}}$ for $1 \leq i, j \leq n$. Then there exists a unique solution $u(t, x)$ to the inhomogeneous heat equation $u_{t}-D \Delta u = f(t, x)$, $(t, x) \in (0, \infty) \times \mathbb{R}$, $u(0, x) = g(x)$, $x \in \mathbb{R}$, existing for $(t, x) \in [0, T) \times \mathbb{R}$. Furthermore, $u(t, x)$ can be represented as $u(t, x)=(\Gamma_{D}(t, \cdot) * g)(x)+\int_{0}^{t}(\Gamma_{D}(t-s, \cdot) * f(s, \cdot))(x) ds$. The solution has the following regularity properties: $u \in C^{0}([0, T) \times \mathbb{R}) \cap C^{1,2}((0, T) \times \mathbb{R})$.

## Depends on

- [Definition 1.0.1 (Class Meeting #5, Section 1 (The Fundamental solution))](../class-meeting-5/013-definition-1-0-1.md)
- [Definition 1.1.1](021-definition-1-1-1.md)
- [Theorem 1.1 (Solving the global Cauchy problem via the fundamental solution)](023-solving-the-global-cauchy-problem-via-th.md)

## Sources

- [MIT 18.152 Introduction to Partial Differential Equations (Fall 2011), Section 1.1](../../../../../sources/v1/IntroductionToPartialDifferentialEquations.md)
