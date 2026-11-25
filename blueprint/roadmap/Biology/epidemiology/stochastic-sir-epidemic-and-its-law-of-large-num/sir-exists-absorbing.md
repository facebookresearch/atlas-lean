# The constructed SIR chain is absorbed after at most $2N$ jumps

Let $\beta, \gamma \ge 0$, let $x_0 = (S_0, I_0)$ be an [SIR state](sirstate.md) with
$S_0 + I_0 \le N$, and let $e_1, e_2$ be sequences of positive interarrival times. Run the
[SIR chain](sir-channels.md) from $x_0$ with the [initial clock configuration](init-clock.md) of
$e_1, e_2$. Then for some $n \le 2N$ the state $(S, I)$ [after $n$ jumps](config.md) is absorbing:
its total rate $\beta S I / N + \gamma I$ is $0$ (with $x / 0 = 0$, so for $N = 0$ the only state
$(0, 0)$ is absorbing).
