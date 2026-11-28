# Duration of a jump of the clock chain

Let $K$ be a [two-channel chain](two-channel.md) on a set $\iota$ with [total rate](total-rate.md)
$q$ and [holding time](hold.md) $h$. The duration of a jump from a state $y$ with residual clocks
$r = (r_1, r_2) \in \mathbb{R}^2$ is

$$d(y, r) = \begin{cases} 0 & \text{if } q(y) = 0, \\ h(y, r) & \text{if } q(y) \ne 0. \end{cases}$$

For a [valid](is-valid.md) chain, $q(y) = 0$ means that both rates vanish and $y$ is absorbing. The
duration can be negative, which for a valid chain requires a negative residual clock.
