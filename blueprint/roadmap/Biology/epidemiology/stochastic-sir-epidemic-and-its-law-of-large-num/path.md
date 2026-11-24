# The path of the clock chain

Let $K$ be a [two-channel chain](two-channel.md) on a set $\iota$ with [rate matrix](rate-matrix.md)
$Q$, $x \in \iota$ and $c$ a [clock configuration](clock-config.md). The path of the clock chain
started at $x$ with clocks $c$ is, for $t \ge 0$, the
[Markov chain path](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-path.md)
$X_t(x, c)$ with matrix $Q$ started at $x$ and driven by the
[steps read off the clock chain](steps.md) with every auxiliary step equal to $(\mathrm{id}, 0)$;
[other auxiliary steps give the same path](ctmc-path-steps.md).

Explicitly, let $(x_n, c_n)$ be the [state and clocks after $n$ jumps](config.md) from $(x, c)$,
$r^{(n)}$ the residual clocks of $c_n$, $q$ the [total rate](total-rate.md) and $h$ the
[holding time](hold.md). The [holding times](ctmc-holding-time-steps.md) are $S_n = \infty$ if
$q(x_n) = 0$ and $S_n = \max(h(x_n, r^{(n)}), 0)$ otherwise, the jump times are
$T_n = S_0 + \dots + S_{n-1}$ (with $T_0 = 0$), and
[between consecutive jump times](path-eq-config.md)

$$X_t(x, c) = x_n \qquad \text{for } T_n \le t < T_{n+1}.$$

If $T_n \le t$ for every $n$ (the jump times accumulate at or before $t$, which requires
$q(x_n) \ne 0$ for every $n$), $X_t(x, c)$ is a fixed state of $\iota$ that does not depend on $x$,
$c$, $t$ or $K$.
