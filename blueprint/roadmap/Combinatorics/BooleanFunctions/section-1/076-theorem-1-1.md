---
article_id: af_00e8b40e6f7228554738d674
declaration: theorem
origin: cited
lean: BooleanFourier.invariance_principle_general
---

# Theorem 1.1 (Section 1 (Motivation and statement))

For all $d \in \mathbb{N}$, if $f(x_1, \ldots, x_n) = \sum_{|S| \leqslant d} \widehat{f}(S) \chi_S(x)$ is a function of degree at most $d$, and $\psi \colon \mathbb{R} \to \mathbb{R}$ is a smooth function with $\|\psi'''\|_\infty \leqslant C$, then $\mathbb{E}_{x \sim \{-1,1\}^n}[\psi(f(x))] - \mathbb{E}_{z \sim N(0, I_n)}[\psi(f(z))] \leqslant \frac{C}{2} \cdot 2^{3d/2} \sum_{i=1}^n I_i[f]^{3/2}$.

## Depends on

- [Definition 2.2 (Lecture 4, Section 2)](../lecture-4/007-definition-2-2.md)

## Proof depends on

- [Claim 5.1](../lecture-4/022-claim-5-1.md)
- [Lemma 3.2](../section-3/080-lemma-3-2.md)

## Sources

- [MIT 18.218 Analysis of Boolean Functions (Spring 2021), Section 1 (Motivation and statement)](../../../../sources/v1/BooleanFunctions.md)
