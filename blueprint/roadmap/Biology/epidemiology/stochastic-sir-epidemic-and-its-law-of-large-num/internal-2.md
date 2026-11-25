# Internal clock of channel 2 after $n$ jumps

Let $K$ be a [two-channel chain](two-channel.md) on a state space $\iota$, with rates
$\mathrm{rate}_1, \mathrm{rate}_2 : \iota \to \mathbb{R}$ (arbitrary real functions), and let
$p = (x, c)$ be a state $x$ with a [clock configuration](clock-config.md) $c$. Write $x_j$ for the
state and $r_j$ for the residual clocks [after $j$ jumps](config.md) from $p$. The internal clock
of channel 2 after $n$ jumps is

$$\tau_2(n) = \sum_{j=0}^{n-1} \mathrm{rate}_2(x_j)\, d(x_j, r_j),$$

where $d(y, r)$ is the [duration of the jump](dur.md) from $y$ with residual clocks $r$: it is
$0$ when the total rate $\mathrm{rate}_1(y) + \mathrm{rate}_2(y)$ is $0$ (an absorbing state) and
the [holding time](hold.md) otherwise. In particular $\tau_2(0) = 0$. When the
durations are nonnegative, $\tau_2(n)$ is the rate of channel 2 integrated over the time taken
by the first $n$ jumps.
