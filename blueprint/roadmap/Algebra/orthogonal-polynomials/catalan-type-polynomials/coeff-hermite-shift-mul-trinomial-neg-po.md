# Hermite-shifted Catalan-type polynomials as convolutions

Write $H_n(x, y) = H^2_n(x, y)$
for the Kampé de Fériet polynomials. For a natural number $m$ and real numbers $\lambda, z$,
write $(1 - m t + z t^m)^{-\lambda}$ and $(1 - m z t + t^m)^{-\lambda}$ for the negative real
powers of the trinomials $1 - m t + z t^m$ and $1 - m z t + t^m$ with exponent $\lambda$ as
power series in $t$ (for $m \ge 1$ these are their expansions in powers of $t$), and let
$P^\lambda_{r,m}(z)$ and $h^\lambda_{r,m}(z)$ be their coefficients of $t^r$. For all natural
numbers $k, m, n$ and real numbers $\lambda, x, y, z$, as formal power series in $t$ (with
$e^{xt + yt^2}$ the exponential series and $H_k(x + 2yt, y)$ evaluated in power series), the
coefficient of $t^n$ in $e^{xt + yt^2} H_k(x + 2yt, y) (1 - m t + z t^m)^{-\lambda}$ is
$\sum_{r=0}^{n} H_{n-r+k}(x, y) P^\lambda_{r,m}(z) / (n - r)!$, and the coefficient of $t^n$
in $e^{xt + yt^2} H_k(x + 2yt, y) (1 - m z t + t^m)^{-\lambda}$ is
$\sum_{r=0}^{n} H_{n-r+k}(x, y) h^\lambda_{r,m}(z) / (n - r)!$.

These coefficients are the paper's $H^{k;\lambda}_{n,m}(x, y, z)$ and
$h^{k;\lambda}_{n,m}(x, y, z)$ (Definition 3, Equations (8) and (9)).

## Sources

- M. A. Pathan and T. Usman, *Unified Catalan-Type Polynomials with Matrix Formulations and Applications*, INTEGERS 26 (2026), Article A105, Theorem 2 (`integers-2026-A105-thm-2`).
