---
article_id: af_37b7dc4f72fe613fb83df03f
declaration: theorem
origin: cited
lean: BooleanFourier.invariance_principle_corollary
---

# Theorem 5.3

For all $C, \varepsilon > 0$, $d \in \mathbb{N}$ there is $\tau > 0$ such that if $f(x_1, \ldots, x_n) = \sum \widehat{f}(S) \chi_S(x)$ is a function such that $\max_i I_i[f^{\leqslant d}] \leqslant \tau$, and $\psi \colon \mathbb{R} \to \mathbb{R}$ is a piecewise smooth $C$-Lipschitz function with $\|\psi'''\|_\infty \leqslant C$, then $\mathbb{E}_{x \sim \{-1,1\}^n}[\psi(f(x))] - \mathbb{E}_{z \sim N(0, I_n)}[\psi(f(z))] \leqslant \varepsilon + 2C\|f^{\geqslant d}\|_2$.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Definition 2.2 (Lecture 4, Section 2)](../lecture-4/007-definition-2-2.md)
- [Claim 5.1](../lecture-4/022-claim-5-1.md)
- [Theorem 1.1 (Section 1 (Motivation and statement))](../section-1/076-theorem-1-1.md)
- [Corollary 5.3](../lecture-4/024-corollary-5-3.md)
- [Theorem 5.1](081-theorem-5-1.md)

## Sources

- [MIT 18.218 Analysis of Boolean Functions (Spring 2021), Section 5.2 (Invariance principle for functions with small Fourier tails)](../../../../sources/v1/BooleanFunctions.md)
