---
article_id: af_b2b771d1603e7731dd0deea4
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Integration.riemann_lebesgue
---

# Lemma (Riemann-Lebesgue) (Fundamental Theorem of Calculus section) (2)

Suppose $f\in C([-\pi, \pi])$ and $f'\in C([-\pi,\pi])$ with $f$ $2\pi$-periodic with $f(-\pi) = f(\pi)$. For $n\in \mathbb{N}\cup \{0\}$, let $a_n = \frac{1}{\pi}\int_{-\pi}^\pi f(x) \sin(nx)\,dx$ and $b_n = \frac{1}{\pi}\int_{-\pi}^\pi f(x) \cos(nx) \,dx$. Then, $\lim_{n\to \infty} a_n = \lim_{n\to \infty} b_n = 0$.

## Depends on

- [Definition (Sequence Convergence of Reals) (Sequences and Series, Sequences and Limits) (1)](../../part-01/sequences-and-series/022-sequence-convergence-of-reals.md)
- [Definition (Section on Derivative)](../../part-01/section-on-derivative/050-definition.md)
- [Definition (C((a,b)))](../the-riemann-integral/064-a-b.md)
- [Theorem (Riemann Integral) (The Riemann Integral section)](../the-riemann-integral/068-riemann-integral.md)

## Proof depends on

- [Theorem (Squeeze Theorem) (Lecture 8, Facts About Limits)](../../part-01/lecture-8/026-squeeze-theorem.md)
- [Theorem (Comparison and Triangle Inequality for Integrals)](../properties-of-the-riemann-integral/077-comparison-and-triangle-inequality-for-i.md)
- [Theorem (Integration by Parts) (Fundamental Theorem of Calculus section) (1)](080-integration-by-parts.md)

## Sources

- [MIT 18.100A Real Analysis (Fall 2020), Fundamental Theorem of Calculus section](../../../../../sources/v1/RealAnalysis.md)
