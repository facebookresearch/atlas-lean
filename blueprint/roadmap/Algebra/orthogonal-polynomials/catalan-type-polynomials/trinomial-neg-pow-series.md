# Negative real power of a trinomial as a power series

For real numbers $\lambda$, $c$,
$\alpha$, $\beta$ and a natural number $m$, this is the formal power series in $t$ with real
coefficients

$$c^{-\lambda} \sum_{n \ge 0} \binom{-\lambda}{n} u^n, \qquad u = \frac{-\alpha t + \beta t^m}{c},$$

that is, the real power $c^{-\lambda}$ times the binomial series
$(1 + t)^{-\lambda} = \sum_{n \ge 0} \binom{-\lambda}{n} t^n$ with $u$ substituted for $t$ (for
$c = 0$ the division is read as $0$, so $u = 0$). The substitution is meaningful when $u$ has
zero constant term, which holds for $m \ge 1$; for $c > 0$ and $m \ge 1$ the series is the
expansion of $(c - \alpha t + \beta t^m)^{-\lambda}$ in powers of $t$.

For $c > 0$ and $m \ge 1$ this is the denominator factor of every generating function in Pathan
and Usman's paper; Section 2 takes $c = 1$, $\alpha = m$ and $\beta = x$.

## Sources

- M. A. Pathan and T. Usman, *Unified Catalan-Type Polynomials with Matrix Formulations and Applications*, INTEGERS 26 (2026), Article A105, Equations (6), (12) and (15).
