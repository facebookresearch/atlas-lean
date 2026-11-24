# Jump times as event times before absorption, for nonnegative durations

Let $K$ be a [two-channel chain](two-channel.md) on a set $\iota$ with [rate matrix](rate-matrix.md)
$Q$ and [total rate](total-rate.md) $q$, $x \in \iota$, $c$ a
[clock configuration](clock-config.md), $f$ any sequence of auxiliary steps and $n \in \mathbb{N}$.
Let $(x_j, c_j)$ be the [state and clocks after $j$ jumps](config.md) from $(x, c)$, $r^{(j)}$ the
residual clocks of $c_j$ and $d_j = d(x_j, r^{(j)})$ the [durations](dur.md). Suppose that

- $q(x_j) \ne 0$ for every $j < n$, and
- $d_j \ge 0$ for every $j \in \mathbb{N}$.

Then the $n$-th
[jump time](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-time.md)
of the [steps read off the clock chain](steps.md) $\omega(x, c, f)$ is the
[event time](event-time.md):

$$T_n\bigl(x, \omega(x, c, f)\bigr) = \tau_n(x, c) = d_0 + \dots + d_{n-1}.$$
