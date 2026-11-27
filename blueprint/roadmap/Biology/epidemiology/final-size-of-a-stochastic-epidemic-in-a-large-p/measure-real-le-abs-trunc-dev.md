# Chebyshev bound for the centered contact count

Let the offspring numbers $\xi_{n,i}$ and the contact targets $U_j$ form a
[final-size epidemic model](is-final-size-epidemic.md) on a probability space $(\Omega, P)$, in the
population $\{0, \dots, N-1\}$, with offspring law $\nu$, a probability measure on $\mathbb{N}$,
with $\int x^2 \, d\nu(x) < \infty$; let $m$ and $\sigma^2$ be its [real mean](offspring-mean.md)
and [real variance](offspring-var.md). For every set $S_0$ of initially susceptible individuals,
every $L \in \mathbb{N}$ and every real $t > 0$,
$P\Bigl(\bigl|T_{m,L}\bigl(w(\omega)\bigr)\bigr| \ge t\Bigr) \le \frac{\sigma^2 L}{t^2}$, where
$T_{m,L}$ is the [centered contact count](trunc-dev.md) and $w(\omega)$ the
[configuration at $\omega$](config-2.md).
