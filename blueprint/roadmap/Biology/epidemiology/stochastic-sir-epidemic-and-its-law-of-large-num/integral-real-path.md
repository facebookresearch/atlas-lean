# Integral of a function of the state along the real path

Let $K$ be a [two-channel chain](two-channel.md) on a finite set $\iota$ with the discrete σ-algebra
and [total rate](total-rate.md) $q$. Let $\varphi : \iota \to \mathbb{R}$, $x \in \iota$ and $c$ a
[clock configuration](clock-config.md), and let $(x_j, c_j)$ be the
[state and clocks after $j$ jumps](config.md) from $(x, c)$, $d_j$ the [durations](dur.md), $\tau_j$
the [event times](event-time.md) and $\tilde X_s(x, c)$ the [real path](real-path.md). Suppose that,
for some $n \in \mathbb{N}$,

- $q(x_j) \ne 0$ for every $j < n$ and $q(x_n) = 0$: the chain is absorbed at the $n$-th state;
- $d_j \ge 0$ for every $j \in \mathbb{N}$.

Let $m \le n$ and $t \in \mathbb{R}$ with $\tau_m \le t$, and also $t \le \tau_{m+1}$ if $m < n$.
Then

$$
\int_0^t \varphi\bigl(\tilde X_s(x, c)\bigr)\, ds
= \sum_{j=0}^{m-1} \varphi(x_j)\, d_j + \varphi(x_m)\,(t - \tau_m):
$$

the sum of $\varphi$ times the durations of the completed jumps, plus $\varphi$ of the current state
times the time elapsed since the last event. For $\varphi$ a channel rate, this is the rate
integrated along the path.
