# Generating function of the partial sums of Chebyshev polynomials

Let
$F_n = 1 + \sum_{k=1}^{n} \bar T_k \in \mathbb{Z}[X]$ be the partial sums of the monic Chebyshev
polynomials $\bar T_k$ ($\bar T_0 = 2$, $\bar T_1 = X$, $\bar T_{k+2} = X \bar T_{k+1} - \bar T_k$).
In the ring $\mathbb{Z}[X][[t]]$ of formal power series in $t$ over $\mathbb{Z}[X]$,

$$(1 - X t + t^2) \sum_{n \ge 0} F_n t^n = 1 + t.$$

Since $1 - X t + t^2$ is a unit in $\mathbb{Z}[X][[t]]$, this is equivalent to
$\sum_{n \ge 0} F_n t^n = (1 + t)/(1 - X t + t^2)$.

## Sources

- C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*, Journal of Integer Sequences 29 (2026), Article 26.4.4, Proposition 3.3 (`jis-2026-26.4.4-prop-8`).
