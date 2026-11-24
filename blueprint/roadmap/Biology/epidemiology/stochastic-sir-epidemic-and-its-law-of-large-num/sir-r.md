# Removed count of the SIR path

For real numbers $\beta, \gamma$, a population size $N$, an initial [SIR state](sirstate.md) $x_0$
and real sequences $e_1, e_2$ of interarrival times, the removed count at a real time $t$ is

$$R(t) = N - S(t) - I(t),$$

with the [susceptible](sir-s.md) and [infective](sir-i.md) counts of the [SIR path](sir-path.md)
and truncated subtraction of natural numbers: $R(t) = 0$ when $S(t) + I(t) > N$. When
$\beta, \gamma \ge 0$, $x_0 = (S_0, I_0)$ has $S_0 + I_0 \le N$ and all interarrival times are
positive, $S(t) + I(t) \le N$ at every time $t \ge 0$
([time-change equations at each time](sir-time-change.md)), so there the subtraction is exact.
