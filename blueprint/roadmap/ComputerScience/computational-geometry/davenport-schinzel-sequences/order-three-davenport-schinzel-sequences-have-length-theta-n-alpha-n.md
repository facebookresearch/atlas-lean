# Order-three Davenport–Schinzel sequences have length $\Theta(n\,\alpha(n))$

Let $\alpha$ be the inverse Ackermann function. Then $\lambda_3(n) = \Theta(n \, \alpha(n))$ (Hart and Sharir).

## Depends on

- [Davenport–Schinzel sequence](davenport-schinzel-sequence.md)

## Expansion

This page becomes ready once:

- Statement prerequisite: the inverse Ackermann function $\alpha(n) = \min\{k : \alpha_k(n) \le 3\}$ with $\alpha_1(n) = \lceil n/2 \rceil$ and, for $k \ge 2$, $\alpha_k(n) = 0$ for $n \le 1$ and $\alpha_k(n) = 1 + \alpha_k(\alpha_{k-1}(n))$ for $n > 1$, as a page of its own.
- Source check: S. Hart and M. Sharir, "Nonlinearity of Davenport–Schinzel sequences and of generalized path compression schemes" (1986), has not been opened. A good expansion separates the upper bound, the lower bound, and the realization of $\Omega(n\alpha(n))$ as the lower envelope of $n$ segments.

## Sources

- D. Halperin and M. Sharir, "Arrangements", Chapter 28 of *Handbook of Discrete and Computational Geometry*, 3rd ed., J. E. Goodman, J. O'Rourke and C. D. Tóth (eds.), CRC Press, 2017, <https://doi.org/10.1201/9781315119601>: Section 28.10, $\lambda_3(n) = 2n\alpha(n) + O(n)$, after S. Pettie, *J. ACM* 62 (2015)
- *Computational Geometry*, lecture notes, ETH Zürich, autumn 2013, Chapter 12 (Davenport–Schinzel sequences), <https://ti.inf.ethz.ch/ew/courses/CG13/lecture/Chapter%2012.pdf>: the paragraph "Bounds for higher-order Davenport-Schinzel sequences" before Section 12.1: the inverse Ackermann hierarchy $\alpha_k$ and the bound $\lambda_3(n) = \Theta(n\alpha(n))$
