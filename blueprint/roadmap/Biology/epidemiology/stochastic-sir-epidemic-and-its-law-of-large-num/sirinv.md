# Bookkeeping invariant of the SIR chain after $n$ jumps

Let $\beta, \gamma$ be real numbers, $N$ a population size, $x_0 = (S_0, I_0)$ an initial
[SIR state](sirstate.md) and $e_1, e_2$ real sequences of interarrival times, with
[arrival times](arrival.md) $A_i(k) = e_i(0) + \dots + e_i(k - 1)$. Run the
[SIR chain](sir-channels.md) from $x_0$ with the [initial clock configuration](init-clock.md) of
$e_1, e_2$, and write, [after $n$ jumps](config.md): $(S_n, I_n)$ for the state, $r_1, r_2$ for
the residual clocks, $u_1, u_2$ for the sequences of future interarrival times, and
$\tau_1(n), \tau_2(n)$ for the internal clocks of [channel 1](internal.md) and
[channel 2](internal-2.md). The invariant after $n$ jumps holds when there are natural numbers
$k_1, k_2$ (read as the numbers of infections and recoveries so far) such that

1. $S_n + k_1 = S_0$ and $I_n + k_2 = I_0 + k_1$;
2. $S_n + I_n \le N$;
3. $u_1(j) = e_1(k_1 + 1 + j)$ and $u_2(j) = e_2(k_2 + 1 + j)$ for every $j \in \mathbb{N}$;
4. $\tau_1(n) + r_1 = A_1(k_1 + 1)$ and $\tau_2(n) + r_2 = A_2(k_2 + 1)$;
5. $A_1(k_1) \le \tau_1(n)$ and $A_2(k_2) \le \tau_2(n)$;
6. $r_1 > 0$ and $r_2 > 0$.

In words: $S_n = S_0 - k_1$ and $I_n = I_0 + k_1 - k_2$ without truncation, with $S_n + I_n \le N$;
the future interarrival times of each clock are those after the ones consumed; each internal clock
plus its residual is the next arrival time of that clock; each internal clock is at least the last
arrival time; and the residuals are positive. The invariant holds for every $n$ when
$\beta, \gamma \ge 0$, $S_0 + I_0 \le N$ and all interarrival times are positive.
