# Kurtz's law of large numbers for stochastic mass-action kinetics

(Kurtz 1972; Ethier–Kurtz 1986, ch. 11, §2.)

Let $(\Omega, P)$ be a probability space, $G$ a
[chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with finite
species set $S$ and finite reaction set $\rho$, and $\kappa \in \mathbb{R}^\rho$ nonnegative rate
constants. For each natural number $N$ and each reaction $r$ let $Y_{N,r}$ be a unit-rate
[Poisson process](../../../Probability/point-processes/poisson-processes/is-poisson-process.md) on
$(\Omega, P)$, with no independence assumed between these processes, and let $X_N$ be random count
paths $\mathbb{R} \to \mathbb{N}^S$ such that, for every $N$ and $P$-almost every $\omega$, the path
$X_N(\omega)$ satisfies the [random time-change equations](is-chain-path.md), driven by the paths
$Y_{N,r}(\cdot, \omega)$, of the [stochastic mass-action network](mass-action.md) at system size
$N$, whose propensities are, for a reaction $r$ with source complex $k = \mathrm{src}(r)$,

$$\lambda^N_r(z) = N \kappa_r \prod_{s \in S} \frac{z_s^{\underline{k_s}}}{N^{k_s}}.$$

Let $x \colon \mathbb{R} \to \mathbb{R}^S$ solve the deterministic mass-action system $x' = f(x)$ at
every $t \ge 0$, with a two-sided derivative also at $t = 0$, where
$f(u) = \sum_r \kappa_r \bigl(\prod_s u_s^{\mathrm{src}(r)_s}\bigr) \zeta_r$, with
$\zeta_r = \mathrm{prod}(r) - \mathrm{src}(r)$, is the
[mass-action vector field](../../../Dynamics/smooth-dynamics/mass-action-field.md). Write
$D_N(t) = \|X_N(t)/N - x(t)\|_1$ for the [deviation](deviation.md), and suppose that
$P(D_N(0) \ge \delta) \to 0$ as $N \to \infty$ for every $\delta > 0$. Then for every real $T$ and
every $\varepsilon > 0$,

$$P\left(\exists\, t \in [0, T],\ D_N(t) \ge \varepsilon\right) \to 0 \quad (N \to \infty).$$

The events are not assumed measurable; $P$ is applied to them as an outer measure. For $T < 0$ the
event is empty. This is
[Kurtz's law of large numbers for density-dependent reaction networks](tendsto-measure-deviation.md)
for the [locally Lipschitz](locally-lipschitz-rate.md) rates
$\beta_r(u) = \kappa_r \prod_s u_s^{\mathrm{src}(r)_s}$, which the scaled propensities approach
[within c/N on bounded sets](abs-mass-action-propensity-div-sub-le.md); the convergence is uniform
on $[0, T]$. When, for a given $N$, the processes $Y_{N,r}$ are independent and $X_N(0)$ is
independent of them, $X_N$ is the stochastic mass-action chain; the theorem assumes neither
independence.
