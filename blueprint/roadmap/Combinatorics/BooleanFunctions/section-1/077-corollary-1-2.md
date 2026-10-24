---
article_id: af_141c6c3bcea5cbf1ab77881a
declaration: theorem
origin: cited
lean: BooleanFourier.invariance_principle_corollary
---

# Corollary 1.2 (Section 1 (Motivation and statement))

For all $C, \varepsilon > 0$, $d \in \mathbb{N}$ there is $\tau > 0$ such that if $f(x_1, \ldots, x_n) = \sum_{|S| \leqslant d} \widehat{f}(S) \chi_S(x)$ is a function of degree at most $d$, $\psi \colon \mathbb{R} \to \mathbb{R}$ is a smooth function with $\|\psi'''\|_\infty \leqslant C$ and $\operatorname{var}(f) \leqslant C$, then $\mathbb{E}_{x \sim \{-1,1\}^n}[\psi(f(x))] - \mathbb{E}_{z \sim N(0, I_n)}[\psi(f(z))] \leqslant \varepsilon$.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Definition 2.2 (Lecture 4, Section 2)](../lecture-4/007-definition-2-2.md)
- [Claim 5.1](../lecture-4/022-claim-5-1.md)
- [Theorem 1.1 (Section 1 (Motivation and statement))](076-theorem-1-1.md)
- [Corollary 5.3](../lecture-4/024-corollary-5-3.md)

## Sources

- [MIT 18.218 Analysis of Boolean Functions (Spring 2021), Section 1 (Motivation and statement)](../../../../sources/v1/BooleanFunctions.md)
