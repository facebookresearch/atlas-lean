# Real path of a chain absorbed after $n$ jumps, between event times

Let $K$ be a [two-channel chain](two-channel.md) on a set $\iota$ with [total rate](total-rate.md)
$q$, $x \in \iota$ and $c$ a [clock configuration](clock-config.md); let $(x_j, c_j)$ be the
[state and clocks after $j$ jumps](config.md) from $(x, c)$, $d_j$ the [durations](dur.md), $\tau_j$
the [event times](event-time.md) and $\tilde X_t(x, c)$ the [real path](real-path.md). Suppose that,
for some $n \in \mathbb{N}$,

- $q(x_j) \ne 0$ for every $j < n$ and $q(x_n) = 0$: the chain is absorbed at the $n$-th state;
- $d_j \ge 0$ for every $j \in \mathbb{N}$.

Let $m \le n$ and $t \in \mathbb{R}$ with $\tau_m \le t$, and also $t < \tau_{m+1}$ if $m < n$. Then
$\tilde X_t(x, c) = x_m$. In particular $\tilde X_t(x, c) = x_n$ for every $t \ge \tau_n$.
