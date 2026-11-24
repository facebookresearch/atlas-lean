# The expected infected fraction converges to the ODE solution

Let $(\Omega, P)$ be a probability space and $\beta, \gamma \ge 0$. For each natural number $N$,
let $Y_{1,N}$ (infection) and $Y_{2,N}$ (recovery) be unit-rate [Poisson processes](../../../Probability/point-processes/poisson-processes/is-poisson-process.md) on
$\Omega$, not necessarily independent, and let $S_N, I_N, R_N$ be random paths such that for
$P$-almost every $\omega$ the paths $(S_N, I_N, R_N)(\omega)$ satisfy the [random time-change equations of the SIR chain](is-chain-path.md) with
population size $N$ and driving functions $Y_{1,N}(\cdot, \omega)$, $Y_{2,N}(\cdot, \omega)$. Let
$(s, i, r)$ be a [solution of the SIR system](../kermack-mckendrick-sir-model/is-solution.md) with population size $1$,
$s' = -\beta s i$, $i' = \beta s i - \gamma i$, $r' = \gamma i$, with $s(0), i(0), r(0) \ge 0$ and
$s(0) + i(0) + r(0) = 1$. Write $D_N(t)$ for the [deviation](deviation.md)
$|S_N(t)/N - s(t)| + |I_N(t)/N - i(t)| + |R_N(t)/N - r(t)|$, and suppose the scaled initial state
converges in probability: $P(D_N(0) \ge \delta) \to 0$ as $N \to \infty$ for every $\delta > 0$,
where the event is not assumed measurable and $P$ is applied to it as an outer measure. Let
$t \ge 0$, and suppose $\omega \mapsto I_N(\omega)(t)$ is measurable for every $N$. Then

$$E[I_N(t)/N] = \int_\Omega \frac{I_N(\omega)(t)}{N}\, dP(\omega) \to i(t) \quad (N \to \infty).$$
