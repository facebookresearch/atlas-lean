# Partial sums of the monic Chebyshev polynomials

For $n \ge 0$, $F_n(X)$ is the
polynomial with integer coefficients

$$F_n(X) = 1 + \sum_{k=1}^{n} \bar T_k(X),$$

where $\bar T_k \in \mathbb{Z}[X]$ is the monic Chebyshev polynomial of the source, that is, the
polynomial with $\bar T_k(q + q^{-1}) = q^k + q^{-k}$; equivalently $\bar T_0 = 2$,
$\bar T_1 = X$ and $\bar T_{k+2} = X \bar T_{k+1} - \bar T_k$. Thus $F_0 = 1$ and
$F_n = F_{n-1} + \bar T_n$ for $n \ge 1$.

## Sources

- C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*, Journal of Integer Sequences 29 (2026), Article 26.4.4, (3.6)–(3.7).
