# Leading coefficients of the partial sums of Chebyshev polynomials

Let
$F_n = 1 + \sum_{k=1}^{n} \bar T_k \in \mathbb{Z}[X]$ be the partial sums of the monic Chebyshev
polynomials $\bar T_k$ ($\bar T_0 = 2$, $\bar T_1 = X$, $\bar T_{k+2} = X \bar T_{k+1} - \bar T_k$).
For every $n \ge 5$, the polynomial

$$F_n - \Big(X^n + X^{n-1} - (n-1) X^{n-2} - (n-2) X^{n-3} + \binom{n-2}{2} X^{n-4} +
\binom{n-3}{2} X^{n-5}\Big)$$

is either zero or has degree less than $n - 5$.

Here $\binom{n-2}{2} = (n-2)(n-3)/2$ and $\binom{n-3}{2} = (n-3)(n-4)/2$.

## Sources

- C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*, Journal of Integer Sequences 29 (2026), Article 26.4.4, Corollary 3.5 (`jis-2026-26.4.4-cor-10`).
