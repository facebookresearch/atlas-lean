# Scaled form of the random time-change equations

Let $C$ be a
[stochastic reaction network](../non-explosion-of-stochastic-reaction-networks/stochastic-crn.md)
with finite reaction set $\rho$ and propensities $\lambda_r$, let
$y_r \colon [0, \infty) \to \mathbb{N}$ be functions, one for each reaction $r$, and let $X$ satisfy
the [random time-change equations](is-chain-path.md) of $C$ driven by the $y_r$. Let $N \ge 1$. Then
for every $t \ge 0$ and every species $i$,

$$\frac{X(t)_i}{N} = \frac{X(0)_i}{N} +
\sum_{r \in \rho} \frac{y_r\bigl(\max(0, N \Lambda_r(t))\bigr)}{N}\, \zeta_r(i),$$

where $\Lambda_r(t) = \frac{1}{N} \int_0^t \lambda_r(X(s))\, ds$ is the
[scaled clock](scaled-clock.md) and $\zeta_r$ the [reaction vector](reaction-vector.md) of $r$. For
$t \ge 0$, $N \Lambda_r(t)$ is the [internal clock](clock.md) of $r$, which is nonnegative, so the
truncation changes nothing.
