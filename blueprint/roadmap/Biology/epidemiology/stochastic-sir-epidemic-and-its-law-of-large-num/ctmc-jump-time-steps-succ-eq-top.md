# After a state of total rate zero the next jump time is infinite

Let $K$ be a [two-channel chain](two-channel.md) on a set $\iota$ with [rate matrix](rate-matrix.md)
$Q$ and [total rate](total-rate.md) $q$, $x \in \iota$, $c$ a
[clock configuration](clock-config.md), $f$ any sequence of auxiliary steps and $n \in \mathbb{N}$.
If the [state after $n$ jumps](config.md) $x_n$ from $(x, c)$ has $q(x_n) = 0$ (for a
[valid](is-valid.md) chain: $x_n$ is absorbing), then the $(n + 1)$-th
[jump time](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-time.md)
of the [steps read off the clock chain](steps.md) $\omega(x, c, f)$ is infinite:

$$T_{n+1}\bigl(x, \omega(x, c, f)\bigr) = \infty.$$
