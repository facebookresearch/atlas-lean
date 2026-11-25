# Kurtz's law of large numbers in supremum form

Let $(\Omega, P)$ be a probability space and $G$ a
[chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with finite
species set $S$ and finite reaction set $\rho$. For each natural number $N$, the system size, let
$C_N$ be a
[stochastic reaction network](../non-explosion-of-stochastic-reaction-networks/stochastic-crn.md) on
$G$ with propensities $\lambda^N_r$. Let $\beta_r \colon \mathbb{R}^S \to \mathbb{R}$, one for each
reaction $r$, be locally Lipschitz functions to which the scaled propensities converge uniformly on
bounded sets: for every real $R$ there are real numbers $e_N \to 0$ such that, for all sufficiently
large $N$, $|\lambda^N_r(z)/N - \beta_r(z/N)| \le e_N$ for every reaction $r$ and every
$z \in \mathbb{N}^S$ with $\|z/N\|_\infty \le R$. For each $N$ and each reaction $r$ let $Y_{N,r}$
be a unit-rate
[Poisson process](../../../Probability/point-processes/poisson-processes/is-poisson-process.md) on
$(\Omega, P)$, with no independence assumed between these processes, and let $X_N$ be random count
paths $\mathbb{R} \to \mathbb{N}^S$ such that, for every $N$ and $P$-almost every $\omega$, the path
$X_N(\omega)$ satisfies the [random time-change equations](is-chain-path.md) of $C_N$ driven by the
paths $Y_{N,r}(\cdot, \omega)$. Let $x$ be a [solution of the mean-field equation](is-solution.md)
$x' = \sum_r \beta_r(x)\, \zeta_r$ of $G$ on $t \ge 0$, write $D_N(t) = \|X_N(t)/N - x(t)\|_1$ for
the [deviation](deviation.md), and suppose that $P(D_N(0) \ge \delta) \to 0$ as $N \to \infty$ for
every $\delta > 0$. Then for every real $T$ and every $\varepsilon > 0$,

$$P\left(\sup_{t \in [0, T]} D_N(t) \ge \varepsilon\right) \to 0 \quad (N \to \infty).$$

The supremum is taken in $[0, \infty]$, so it exists for every path, bounded or not, and need not be
attained; for $T < 0$ it is $0$ and the event is empty. The event lies inside
$\{\exists\, t \in [0, T],\ D_N(t) \ge \varepsilon/2\}$, whose outer measure tends to $0$ by
[Kurtz's law of large numbers](tendsto-measure-deviation.md). Neither it nor the events
$\{D_N(0) \ge \delta\}$ of the hypothesis are assumed measurable, and $P$ is applied to them as an
outer measure.
