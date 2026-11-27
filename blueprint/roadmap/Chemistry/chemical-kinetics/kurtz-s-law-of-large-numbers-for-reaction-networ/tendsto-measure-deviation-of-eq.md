# Kurtz's theorem for exactly density-dependent propensities

(Kurtz 1970.)

Let $(\Omega, P)$ be a probability space and $G$ a
[chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with finite
species set $S$ and finite reaction set $\rho$. For each natural number $N$, the system size, let
$C_N$ be a
[stochastic reaction network](../non-explosion-of-stochastic-reaction-networks/stochastic-crn.md) on
$G$ with propensities $\lambda^N_r$. Let $\beta_r \colon \mathbb{R}^S \to \mathbb{R}$, one for each
reaction $r$, be locally Lipschitz functions such that, for every $N \ge 1$, every reaction $r$ and
every $z \in \mathbb{N}^S$,

$$\lambda^N_r(z) = N \beta_r(z/N).$$

For each $N$ and each reaction $r$ let $Y_{N,r}$ be a unit-rate
[Poisson process](../../../Probability/point-processes/poisson-processes/is-poisson-process.md) on
$(\Omega, P)$, with no independence assumed between these processes, and let $X_N$ be random count
paths $\mathbb{R} \to \mathbb{N}^S$ such that, for every $N$ and $P$-almost every $\omega$, the path
$X_N(\omega)$ satisfies the [random time-change equations](is-chain-path.md) of $C_N$ driven by the
paths $Y_{N,r}(\cdot, \omega)$. Let $x$ be a [solution of the mean-field equation](is-solution.md)
$x' = \sum_r \beta_r(x)\, \zeta_r$ of $G$ on $t \ge 0$, write $D_N(t) = \|X_N(t)/N - x(t)\|_1$ for
the [deviation](deviation.md), and suppose that $P(D_N(0) \ge \delta) \to 0$ as $N \to \infty$ for
every $\delta > 0$. Then for every real $T$ and every $\varepsilon > 0$,

$$P\left(\exists\, t \in [0, T],\ D_N(t) \ge \varepsilon\right) \to 0 \quad (N \to \infty).$$

The events are not assumed measurable; $P$ is applied to them as an outer measure. Nothing is
assumed of $C_0$. For $N \ge 1$ the scaled propensities are exactly $\beta_r(z/N)$, so the uniform
approximation required by
[Kurtz's law of large numbers for density-dependent reaction networks](tendsto-measure-deviation.md)
holds with error $0$.
