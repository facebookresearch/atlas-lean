---
article_id: af_48c5c59432ee5ddfac26310d
declaration: theorem
origin: cited
lean: BooleanFourier.invariance_principle_corollary
---

# Theorem 5.1

For all $d \in \mathbb{N}$, $\varepsilon > 0$ there is $\tau > 0$ such that if $f(x_1, \ldots, x_n) = \sum_{|S| \leqslant d} \widehat{f}(S) \chi_S(x)$ is a function of degree at most $d$, and $\max_i I_i[f] \leqslant \tau$, then $\mathbb{E}_{x \sim \{-1,1\}^n}[\psi_0(f(x))] - \mathbb{E}_{z \sim N(0, I_n)}[\psi_0(f(z))] \leqslant \varepsilon$.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Definition 2.2 (Lecture 4, Section 2)](../lecture-4/007-definition-2-2.md)
- [Claim 5.1](../lecture-4/022-claim-5-1.md)
- [Theorem 1.1 (Section 1 (Motivation and statement))](../section-1/076-theorem-1-1.md)
- [Corollary 5.3](../lecture-4/024-corollary-5-3.md)
- [Theorem 5.2](082-theorem-5-2.md)

## Sources

- [MIT 18.218 Analysis of Boolean Functions (Spring 2021), Section 5.1 (Invariance principle for non-smooth test functions)](../../../../sources/v1/BooleanFunctions.md)
