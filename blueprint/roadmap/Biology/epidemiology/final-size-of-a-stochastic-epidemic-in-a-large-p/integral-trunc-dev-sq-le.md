# The centered contact count has second moment at most $\sigma^2 L$

Let the offspring numbers $\xi_{n,i}$ and the contact targets $U_j$ form a
[final-size epidemic model](is-final-size-epidemic.md) on a probability space $(\Omega, P)$, in the
population $\{0, \dots, N-1\}$, with offspring law $\nu$, a probability measure on $\mathbb{N}$,
with $\int x^2 \, d\nu(x) < \infty$; let $m$ and $\sigma^2$ be its [real mean](offspring-mean.md)
and [real variance](offspring-var.md). For every set $S_0$ of initially susceptible individuals and
every $L \in \mathbb{N}$, $\int T_{m,L}\bigl(w(\omega)\bigr)^2 \, dP(\omega) \le \sigma^2 L$, where
$T_{m,L}$ is the [centered contact count](trunc-dev.md) and $w(\omega)$ the
[configuration at $\omega$](config-2.md). The integrand is integrable under these hypotheses, so the
left side is the second moment of $T_{m,L}(w)$. The terms of distinct individuals are orthogonal,
and the [gates add up to at most $L$](sum-gate-le.md).
