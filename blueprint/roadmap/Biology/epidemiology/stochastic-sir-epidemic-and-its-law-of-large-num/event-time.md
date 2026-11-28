# Real event times of the clock chain

Let $K$ be a [two-channel chain](two-channel.md) on a set $\iota$, $x \in \iota$ and $c$ a
[clock configuration](clock-config.md); let $(x_j, c_j)$ be the
[state and clocks after $j$ jumps](config.md) from $(x_0, c_0) = (x, c)$ and $r^{(j)}$ the residual
clocks of $c_j$. The time of the $n$-th event is the real number

$$\tau_n(x, c) = \sum_{j=0}^{n-1} d(x_j, r^{(j)}),$$

the sum of the [durations](dur.md) of the first $n$ jumps, with $\tau_0(x, c) = 0$. A jump from a
state of [total rate](total-rate.md) $0$ has duration $0$ and leaves the state and the clocks
unchanged, so once the chain reaches such a state its event times stay constant.
