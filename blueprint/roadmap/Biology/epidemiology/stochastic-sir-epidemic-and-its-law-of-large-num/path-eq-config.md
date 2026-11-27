# Between consecutive jump times the path is the current state

Let $K$ be a [two-channel chain](two-channel.md) on a set $\iota$ with [total rate](total-rate.md)
$q$ and [holding time](hold.md) $h$, $x \in \iota$ and $c$ a [clock configuration](clock-config.md);
let $(x_k, c_k)$ be the [state and clocks after $k$ jumps](config.md) from $(x, c)$ and $r^{(k)}$
the residual clocks of $c_k$. Let $T_m = S_0 + \dots + S_{m-1}$ be the
[jump times](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-time.md)
of the [steps read off the clock chain](steps.md), with [holding times](ctmc-holding-time-steps.md)
$S_k = \infty$ if $q(x_k) = 0$ and $S_k = \max(h(x_k, r^{(k)}), 0)$ otherwise. For $t \ge 0$ and
$m \in \mathbb{N}$, if $T_m \le t < T_{m+1}$, the [path of the clock chain](path.md) is the state
after $m$ jumps:

$$X_t(x, c) = x_m.$$
