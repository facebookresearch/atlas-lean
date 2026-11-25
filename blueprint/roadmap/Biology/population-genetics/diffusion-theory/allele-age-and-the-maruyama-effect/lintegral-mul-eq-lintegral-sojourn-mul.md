# Mean time as a sum of sojourn times

Let $w(p, x, t) \in [0, \infty]$, for real $p$, $x$, $t$, be jointly measurable and satisfy the Chapman–Kolmogorov equation for positive times:

$$w(p, x, s + t) = \int_{(0,1)} w(p, y, s)\, w(y, x, t)\, dy \quad \text{for all } p, x \text{ and all } s, t > 0.$$

Then for all real $p$ and $x$, in $[0, \infty]$,

$$\int_0^\infty t\, w(p, x, t)\, dt = \int_{(0,1)} \Bigl(\int_0^\infty w(p, y, s)\, ds\Bigr)\Bigl(\int_0^\infty w(y, x, t)\, dt\Bigr) dy.$$

With $\Psi(p, x) = \int_0^\infty w(p, x, t)\, dt$, dividing by $\Psi(p, x)$ reads $\int_0^1 \Psi(p, y)\Psi(y, x)/\Psi(p, x)\, dy$, the integral of the [conditional sojourn density](age-density.md) when $\Psi$ is the [sojourn density](selection-green.md), as a mean time. The function $w$ is arbitrary; it need not be the Wright–Fisher transition density.

## Sources

- T. Maruyama and M. Kimura, *Moments for sum of an arbitrary function of gene frequency along a stochastic path of gene frequency change*, Proc. Natl. Acad. Sci. USA 72 (1975), 1602–1604.
