# Internal clock of a reaction along a count path

Let $C$ be a
[stochastic reaction network](../non-explosion-of-stochastic-reaction-networks/stochastic-crn.md) on
a species set $S$, with propensities $\lambda_r \ge 0$. For a count path
$X \colon \mathbb{R} \to \mathbb{N}^S$, a reaction $r$ and a real time $t$, the internal clock of
$r$ at time $t$ is the propensity integrated along the path, truncated at $0$:

$$\tau_r(t) = \max\left(0, \int_0^t \lambda_r(X(s))\, ds\right) \in [0, \infty).$$

The integral is oriented, $\int_0^t = -\int_t^0$ for $t < 0$, and by convention it is $0$ when
$s \mapsto \lambda_r(X(s))$ is not integrable on the interval between $0$ and $t$. Since
$\lambda_r \ge 0$, the truncation changes nothing for $t \ge 0$, and $\tau_r(t) = 0$ for $t \le 0$.
Being a nonnegative number, the clock can index a counting process, as in the
[random time-change equations](is-chain-path.md).
