# With i.i.d. Exp(1) interarrival times, the recovery clock is a rate-one Poisson process

Under the [clock law](clock-law.md) $\mathbb{P}$ on pairs $(e_1, e_2)$ of real sequences, the
[counting path](clock-count.md) $Y_2$ of the second sequence $e_2$ (the recovery clock) is a
[Poisson process](../../../Probability/point-processes/poisson-processes/is-poisson-process.md)
of rate 1 indexed by $u \ge 0$: $Y_2(0) = 0$ almost surely, almost every path $u \mapsto Y_2(u)$
is nondecreasing, the increments over consecutive intervals are independent, and for
$0 \le s \le u$ the increment $Y_2(u) - Y_2(s)$ has the Poisson law of mean $u - s$.
