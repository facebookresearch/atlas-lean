# With i.i.d. Exp(1) interarrival times, the infection clock is a rate-one Poisson process

Under the [clock law](clock-law.md) $\mathbb{P}$ on pairs $(e_1, e_2)$ of real sequences, the
[counting path](clock-count.md) $Y_1$ of the first sequence $e_1$ (the infection clock) is a
[Poisson process](../../../Probability/point-processes/poisson-processes/is-poisson-process.md)
of rate 1 indexed by $u \ge 0$: $Y_1(0) = 0$ almost surely, almost every path $u \mapsto Y_1(u)$
is nondecreasing, the increments over consecutive intervals are independent, and for
$0 \le s \le u$ the increment $Y_1(u) - Y_1(s)$ has the Poisson law of mean $u - s$.
