# A jump of the SIR chain from an active state lowers $2S + I$

Let $\beta, \gamma \ge 0$ and let $y = (S, I)$ be an [SIR state](sirstate.md) with $S + I \le N$
and nonzero total rate $\beta S I / N + \gamma I$ (for $N = 0$ the only state is $(0, 0)$, whose
total rate is $0$ by the convention $x / 0 = 0$). For residual clocks $r_1 > 0$ and $r_2 > 0$, the
state $(S', I')$ after the [next jump](next.md) of the [SIR chain](sir-channels.md) from $y$
satisfies

$$2 S' + I' < 2 S + I.$$
