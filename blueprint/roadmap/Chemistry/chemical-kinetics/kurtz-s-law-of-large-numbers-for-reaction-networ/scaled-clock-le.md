# A bound on the scaled propensities bounds the scaled clock

Let $C$ be a
[stochastic reaction network](../non-explosion-of-stochastic-reaction-networks/stochastic-crn.md)
with finite reaction set and propensities $\lambda_r$, and let $X$ satisfy the
[random time-change equations](is-chain-path.md) of $C$ driven by some functions $y_r$. Let
$N \ge 1$, $r$ a reaction, $t \ge 0$ and $B$ real. If $\lambda_r(X(s))/N \le B$ for every
$s \in (0, t)$, then the [scaled clock](scaled-clock.md) satisfies

$$\Lambda_r(t) = \frac{1}{N} \int_0^t \lambda_r(X(s))\, ds \le B t.$$

Of the time-change equations only the integrability of the propensities along the path is used.
