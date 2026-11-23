# Odd-divisor formula for the Kassel–Reutenauer polynomials

Let $n \ge 1$, and for each
odd divisor $d$ of $n$ put $r_n(d) = n/d - (d+1)/2$, an integer. Then the Kassel–Reutenauer
polynomial $\bar P_n$ satisfies

$$
\bar P_n(X) = \sum_{d \mid n,\ d \text{ odd},\ r_n(d) \ge 0} F_{r_n(d)}(X) -
\sum_{d \mid n,\ d \text{ odd},\ r_n(d) < 0} F_{-r_n(d)-1}(X),
$$

where $F_r(X) = 1 + \sum_{k=1}^{r} \bar T_k(X)$ is the partial sum of the monic Chebyshev
polynomials $\bar T_k$.

## Sources

- C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*, Journal of Integer Sequences 29 (2026), Article 26.4.4, Theorem 4.4 (`jis-2026-26.4.4-thm-16`).
