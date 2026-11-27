# The SIR path driven by two unit clocks

For real numbers $\beta, \gamma$, a population size $N$, an initial [SIR state](sirstate.md) $x_0$
and real sequences $e_1, e_2$ (the interarrival times of the infection and recovery clocks), the
SIR path at a real time $t$ is

$$X(t) = X_K(x_0, c)\bigl(\max(t, 0)\bigr),$$

the [path](path.md) $X_K(x_0, c)$ of the [SIR two-channel chain](sir-channels.md) $K$ started at
$x_0$ with the [initial clock configuration](init-clock.md) $c$ of $e_1, e_2$, taken at time
$\max(t, 0)$ (the [path on the real line](real-path.md)). Thus $X(t) = X(0)$ for $t < 0$. For
$t \ge 0$, if only finitely many jumps of the chain occur by time $t$, $X(t)$ is the state after
the last of them ($x_0$ if there is none); if infinitely many occur by time $t$, $X(t)$ is a fixed
state that depends only on $N$.

When $\beta, \gamma \ge 0$, $x_0 = (S_0, I_0)$ has $S_0 + I_0 \le N$ and all interarrival times are
positive, the chain is [absorbed after at most $2N$ jumps](sir-exists-absorbing.md), so the second
case does not occur; the path then [starts at $x_0$](sir-path-zero.md) and its counts solve the
[time-change equations](is-chain-path-sir.md).
