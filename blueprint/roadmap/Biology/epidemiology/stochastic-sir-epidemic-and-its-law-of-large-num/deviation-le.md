# Kurtz's pathwise estimate for the SIR chain

Let $N \ge 1$, $\beta \ge 0$ and $\gamma \ge 0$, and let $(S, I, R)$ satisfy the [random time-change equations of the SIR chain](is-chain-path.md)
with population size $N$ and driving functions $y_1$, $y_2$. Let $(s, i, r)$ be a
[solution of the SIR system](../kermack-mckendrick-sir-model/is-solution.md) with population size $1$,
$s' = -\beta s i$, $i' = \beta s i - \gamma i$, $r' = \gamma i$, started in the simplex:
$s(0), i(0), r(0) \ge 0$ and $s(0) + i(0) + r(0) = 1$. Let $T$ and $\eta$ be real, and suppose the
scaled driving counts stay within $\eta$ of the identity on the clock ranges:
$|y_1(N a)/N - a| \le \eta$ for every $a \in [0, \beta T]$ and $|y_2(N a)/N - a| \le \eta$ for every
$a \in [0, \gamma T]$. Then the [deviation](deviation.md) $D$ of $(S, I, R)/N$ from $(s, i, r)$
satisfies, for every $t \in [0, T]$,

$$D(t) \le (D(0) + 4 \eta)\, e^{2 (\beta + \gamma) t}.$$

Proof: subtracting the integral form of the ODE from the time-change equations leaves the
initial error, the clock errors (at most $\eta$ each), and the integral of the drift difference,
which is $2 (\beta + \gamma)$-Lipschitz in $\ell^1$ on the simplex; Gronwall's inequality closes
it.
