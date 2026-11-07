# Nieto–Hermite Catalan-type polynomials as convolutions

Let $j, k, m, r$ be natural
numbers with $k \le r$ and let $\lambda, x, y$ be real numbers. Let $E(t) = e^{2yt - t^2}$ be the
exponential series, so that its coefficient of $t^n$ is $H_n(y) / n!$ with $H_n$ the Hermite
polynomials, and let $F(t)$ be the power series whose coefficient of $t^n$ is $H_n(y) / n!$ when
$n \ge k$ and $j \mid n - k$, and $0$ otherwise (for $j \ge 1$ this is the series
$F(j, k, y, t) = \sum_n H_{jn+k}(y) t^{jn+k} / (jn + k)!$ of Equation (1)). Write
$(1 - m t + x t^m)^{-\lambda}$ and $(1 - m x t + t^m)^{-\lambda}$ for the negative real powers
of the trinomials $1 - m t + x t^m$ and $1 - m x t + t^m$ with exponent $\lambda$ as power
series in $t$ (for $m \ge 1$ these are their expansions in powers of $t$), let
$P^\lambda_{s,m}(x)$ and $h^\lambda_{s,m}(x)$ be their coefficients of $t^s$, and let
$q = \lfloor (r - k) / j \rfloor$, read as $q = 0$ when $j = 0$. Then the coefficient of
$t^r$ in $F(t) (1 - m t + x t^m)^{-\lambda}$ is
$\sum_{n=0}^{q} H_{jn+k}(y) P^\lambda_{r-jn-k,m}(x) / (jn + k)!$, and the coefficient of $t^r$
in $F(t) (1 - m x t + t^m)^{-\lambda}$ is the same sum with $h^\lambda_{r-jn-k,m}(x)$ in place
of $P^\lambda_{r-jn-k,m}(x)$.

These are the paper's $F^{j.k;\lambda}_{r,m}(x, y)$ and $f^{j.k;\lambda}_{r,m}(x, y)$
(Equations (10) and (11)). The paper takes $j, m \ge 1$; for $r < k$ its sum is empty.

## Sources

- M. A. Pathan and T. Usman, *Unified Catalan-Type Polynomials with Matrix Formulations and Applications*, INTEGERS 26 (2026), Article A105, Theorem 3 (`integers-2026-A105-thm-3`).
