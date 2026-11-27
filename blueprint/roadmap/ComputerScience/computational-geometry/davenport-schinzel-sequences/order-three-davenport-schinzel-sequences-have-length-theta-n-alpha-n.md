# Order-three Davenport–Schinzel sequences have length $\Theta(n\,\alpha(n))$

Let $\alpha$ be the [inverse Ackermann function](inverse-ackermann-function.md). There are constants $c_1, c_2 > 0$ such that the maximum length $\lambda_3(n)$ of an order-three Davenport–Schinzel sequence over $n$ symbols satisfies $c_1\, n\, \alpha(n) \le \lambda_3(n) \le c_2\, n\, \alpha(n)$ for all $n \ge 1$ (Hart and Sharir).

## Depends on

- [Davenport–Schinzel sequence](davenport-schinzel-sequence.md)
- [Inverse Ackermann function](inverse-ackermann-function.md)

## Sources

- S. Pettie, "Sharp Bounds on Davenport–Schinzel Sequences of Every Order", *Journal of the ACM* 62(5), Article 36, 2015, <https://doi.org/10.1145/2794075>: Theorem 1.3 at $s = 3$, $\lambda_3(n) = 2n\alpha(n) + O(n)$ (Theorem 1.2 in the author copy arXiv:1204.1086, <https://arxiv.org/abs/1204.1086>).
- *Computational Geometry*, lecture notes, ETH Zürich, autumn 2013, Chapter 12 (Davenport–Schinzel sequences), <https://ti.inf.ethz.ch/ew/courses/CG13/lecture/Chapter%2012.pdf>: the paragraph "Bounds for higher-order Davenport-Schinzel sequences" (p. 138), for the convention used here for the inverse Ackermann hierarchy $\alpha_k$ and $\alpha(n) = \min\{k \mid \alpha_k(n) \le 3\}$.
