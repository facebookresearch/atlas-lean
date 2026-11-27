# Kurtz's law of large numbers for density-dependent reaction networks

(Kurtz 1970, Thm 3.1; Ethier–Kurtz 1986, ch. 11, Thm 2.1.)

Let $(\Omega, P)$ be a probability space and $G$ a
[chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with finite
species set $S$ and finite reaction set $\rho$. For each natural number $N$, the system size, let
$C_N$ be a
[stochastic reaction network](../non-explosion-of-stochastic-reaction-networks/stochastic-crn.md) on
$G$ with propensities $\lambda^N_r$. Let $\beta_r \colon \mathbb{R}^S \to \mathbb{R}$, one for each
reaction $r$, be locally Lipschitz functions to which the scaled propensities converge uniformly on
bounded sets: for every real $R$ there are real numbers $e_N \to 0$ such that, for all sufficiently
large $N$,

$$\left|\lambda^N_r(z)/N - \beta_r(z/N)\right| \le e_N$$

for every reaction $r$ and every $z \in \mathbb{N}^S$ whose [scaled state](scaled.md) has sup norm
$\|z/N\|_\infty \le R$. For each $N$ and each reaction $r$ let $Y_{N,r}$ be a unit-rate
[Poisson process](../../../Probability/point-processes/poisson-processes/is-poisson-process.md) on
$(\Omega, P)$, with no independence assumed between these processes, and let $X_N$ be random count
paths $\mathbb{R} \to \mathbb{N}^S$ such that, for every $N$ and $P$-almost every $\omega$, the path
$X_N(\omega)$ satisfies the [random time-change equations](is-chain-path.md) of $C_N$ driven by the
paths $Y_{N,r}(\cdot, \omega)$. Let $x$ be a [solution of the mean-field equation](is-solution.md)
$x' = \sum_r \beta_r(x)\, \zeta_r$ of $G$ on $t \ge 0$, write $D_N(t) = \|X_N(t)/N - x(t)\|_1$ for
the [deviation](deviation.md), and suppose that the scaled initial state converges in probability:
$P(D_N(0) \ge \delta) \to 0$ as $N \to \infty$ for every $\delta > 0$. Then for every real $T$ and
every $\varepsilon > 0$,

$$P\left(\exists\, t \in [0, T],\ D_N(t) \ge \varepsilon\right) \to 0 \quad (N \to \infty).$$

The events are not assumed measurable; $P$ is applied to them as an outer measure. For $T < 0$ the
event is empty. It contains the event that the supremum of $D_N$ over $[0, T]$ exceeds
$\varepsilon$, so the scaled paths converge to $x$ in probability uniformly on $[0, T]$, not only at
each fixed time; the event that this supremum is at least $\varepsilon$ is treated in the
[supremum form](tendsto-measure-i-sup-deviation.md). When, for a given $N$, the processes $Y_{N,r}$
($r \in \rho$) are independent and the initial state $X_N(0)$ is independent of them, $X_N$ is the
continuous-time Markov chain in which reaction $r$ fires at rate $\lambda^N_r(X_N)$; the theorem
assumes neither independence.

Proof: $x$ is continuous on $[0, \infty)$, so $x([0, T])$ is compact and the $\beta_r$ are Lipschitz
and bounded on a neighbourhood of it, which bounds the scaled propensities there for large $N$. Off
the null sets where the time-change equations fail, [Kurtz's pathwise estimate](deviation-le.md)
puts the event, for large $N$, inside the union of $\{D_N(0) \ge \delta_0\}$ and of the events
$\{\exists\, a \in [0, (B + 1) T],\ |Y_{N,r}(N a)/N - a| > \eta\}$, for suitable
$\delta_0, \eta > 0$ and $B \ge 0$; the initial condition and the
[uniform law of large numbers for unit Poisson clocks](../../../Biology/epidemiology/stochastic-sir-epidemic-and-its-law-of-large-num/tendsto-measure-poisson-clock.md)
make their outer measures tend to $0$.
