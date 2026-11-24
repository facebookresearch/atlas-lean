# Jumps of the constructed SIR chain take nonnegative time

Let $\beta, \gamma \ge 0$, let $x_0 = (S_0, I_0)$ be an [SIR state](sirstate.md) with
$S_0 + I_0 \le N$, and let $e_1, e_2$ be sequences of positive interarrival times. Run the
[SIR chain](sir-channels.md) from $x_0$ with the [initial clock configuration](init-clock.md) of
$e_1, e_2$. For every $j \in \mathbb{N}$, the [duration](dur.md) of the jump from the state
[after $j$ jumps](config.md), with the residual clocks at that point, is nonnegative. (By
definition, the duration is $0$ from an absorbing state.)
