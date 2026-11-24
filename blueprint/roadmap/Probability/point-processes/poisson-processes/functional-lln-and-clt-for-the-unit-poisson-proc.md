# Functional law of large numbers for the unit Poisson process

Let $Y$ be a [Poisson process](is-poisson-process.md) of rate $1$ with nondecreasing paths. Then for every $T > 0$,

$$\sup_{0 \le t \le T} \Bigl| \frac{Y(Nt)}{N} - t \Bigr| \longrightarrow 0 \quad \text{almost surely as } N \to \infty .$$

For each fixed rational $t$, $Y(Nt)/N \to t$ almost surely by the [strong law of large numbers](../../../Dynamics/ergodic-theory/birkhoff-ergodic-theorem/tendsto-average-coordinates-ae.md) applied to the independent $\mathrm{Poisson}(t)$ increments
$Y((k+1)t) - Y(kt)$, $k < N$, which are independent and identically distributed by the definition of a Poisson process, so the
strong law on the coordinates of the product space transfers to them through their joint law (for integer $N$; real $N$ follow by
monotonicity, from $Y(\lfloor N \rfloor t) \le Y(Nt) \le Y((\lfloor N \rfloor + 1)t)$); on the event of probability $1$ where this holds for all rationals in a grid of
mesh $\delta$, monotonicity of $Y$ gives $\limsup_N \sup_{t \le T} |Y(Nt)/N - t| \le \delta$, and $\delta$ is arbitrary.

## Depends on

- [Poisson process](is-poisson-process.md)

## Proof depends on

- [Strong law of large numbers from the ergodic theorem](../../../Dynamics/ergodic-theory/birkhoff-ergodic-theorem/tendsto-average-coordinates-ae.md)

## Expansion

The functional central limit theorem, $(Y(Nt) - Nt)/\sqrt N \to$ standard Brownian motion in distribution in the Skorokhod space $D[0, T]$, is a
separate statement that needs Donsker's invariance principle and the Skorokhod topology.

## Sources

- P. Billingsley, *Convergence of Probability Measures*, 2nd ed., Wiley (1999). The functional law is derived above.
