# The SIR epidemic as a two-channel chain

For real numbers $\beta, \gamma$ and a population size $N$, the SIR epidemic is the
[two-channel chain](two-channel.md) on the [SIR states](sirstate.md) $(S, I)$ in which

- channel 1 (infection) has rate $\beta S I / N$ and moves $(S, I)$ to $(S - 1, \min(I + 1, N))$;
- channel 2 (recovery) has rate $\gamma I$ and moves $(S, I)$ to $(S, I - 1)$;
- an infection and a recovery at the same instant move $(S, I)$ to $(S - 1, I)$.

Here $S - 1$ and $I - 1$ are truncated subtractions of natural numbers, so $0 - 1 = 0$. On a state
with $S + I \le N$, infection leads to $(S - 1, I + 1)$ when $S \ge 1$ and recovery leads to
$(S, I - 1)$ when $I \ge 1$; otherwise the channel's rate is $0$. For $N = 0$ the only state is
$(0, 0)$, whose infection rate is $0$ by the convention $x / 0 = 0$. The definition allows any real
$\beta, \gamma$; for $\beta \ge 0$ and $\gamma \ge 0$ the rates are nonnegative and the chain is
[valid](is-valid.md).
