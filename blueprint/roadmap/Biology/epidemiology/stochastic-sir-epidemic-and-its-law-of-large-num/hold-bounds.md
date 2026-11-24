# Holding-time bounds from an active state with positive residuals

Let $K$ be a [valid](is-valid.md) [two-channel chain](two-channel.md) on a set $\iota$, so that its
rates $\lambda_1, \lambda_2$ are nonnegative, with [total rate](total-rate.md)
$q = \lambda_1 + \lambda_2$ and [holding time](hold.md) $h$. For an active state $y$, $q(y) \ne 0$,
and residual clocks $r = (r_1, r_2)$ with $r_1 > 0$ and $r_2 > 0$,

$$h(y, r) > 0, \qquad \lambda_1(y)\, h(y, r) \le r_1, \qquad \lambda_2(y)\, h(y, r) \le r_2:$$

the jump takes a positive time, during which neither channel consumes more internal time than its
residual clock.
