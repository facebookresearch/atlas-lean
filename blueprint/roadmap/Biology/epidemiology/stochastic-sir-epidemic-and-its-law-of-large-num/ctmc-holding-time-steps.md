# Holding times of the steps read off the clock chain

Let $K$ be a [two-channel chain](two-channel.md) on a set $\iota$ with [rate matrix](rate-matrix.md)
$Q$, [total rate](total-rate.md) $q$ and [holding time](hold.md) $h$. Let $x \in \iota$, $c$ a
[clock configuration](clock-config.md), $g$ any sequence of auxiliary steps and $\omega$ the
[steps read off the clock chain](steps.md) started at $x$ with clocks $c$ and auxiliary steps $g$.
With $(x_n, c_n)$ the [state and clocks after $n$ jumps](config.md) from $(x, c)$ and $r^{(n)}$ the
residual clocks of $c_n$, the $n$-th
[holding time](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-holding-time.md)
of $\omega$ for $Q$ is

$$
S_n(x, \omega) = \begin{cases} \infty & \text{if } q(x_n) = 0, \\
\max\bigl(h(x_n, r^{(n)}), 0\bigr) & \text{if } q(x_n) \ne 0, \end{cases}
$$

in $[0, \infty]$: infinite at a state of total rate $0$, and otherwise the holding time of the clock
chain, replaced by $0$ when it is negative. It does not depend on the auxiliary steps.
