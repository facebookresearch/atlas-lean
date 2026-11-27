# Probabilistic backward error of inner products

Let $a, b \in \mathbb{R}^n$ and let $\hat y$ be the value of $y = a^T b$ computed in floating-point arithmetic, in any order of summation, under the [probabilistic model of rounding errors](probabilistic-model-of-rounding-errors.md). Then for $\lambda > 0$,

$$\hat y = (a + \Delta a)^T b = a^T (b + \Delta b), \qquad |\Delta a| \le \tilde\gamma_n(\lambda) |a|, \quad |\Delta b| \le \tilde\gamma_n(\lambda) |b|$$

(componentwise), with probability at least $Q(\lambda, n) = 1 - n(1 - P(\lambda))$, where $\tilde\gamma_n$ and $P$ are as in the [probabilistic product bound](probabilistic-product-bound-under-mean-independence.md). When $nu < 1$, the deterministic analysis gives the same statement with $\gamma_n = nu/(1 - nu)$ in place of $\tilde\gamma_n(\lambda) = \lambda\sqrt n\,u + O(u^2)$, and with certainty; the probabilistic statement needs no such condition.

## Depends on

- [Probabilistic model of rounding errors](probabilistic-model-of-rounding-errors.md)
- [Floating-point dot product](../dot-fl.md)
- [Probabilistic product bound under mean independence](probabilistic-product-bound-under-mean-independence.md)
- [The constant γₙ of rounding error analysis](../gamma.md)

## Proof depends on

- [Probabilistic product bound under mean independence](probabilistic-product-bound-under-mean-independence.md)

## Sources

- N. J. Higham and T. Mary, "A new approach to probabilistic rounding error analysis", *SIAM J. Sci. Comput.* 41(5):A2815–A2835, 2019; MIMS EPrint 2018.33, Section 3, the definition (3.1) of $Q(\lambda, n)$ and Theorem 3.1 with its proof through (3.4)–(3.5) and a union bound over the $n$ terms. <https://eprints.maths.manchester.ac.uk/2673/1/paper.pdf>
