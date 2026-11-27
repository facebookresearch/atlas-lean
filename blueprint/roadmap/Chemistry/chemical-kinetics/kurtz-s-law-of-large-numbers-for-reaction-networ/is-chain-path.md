# Random time-change equations of a stochastic reaction network

Let $C$ be a
[stochastic reaction network](../non-explosion-of-stochastic-reaction-networks/stochastic-crn.md) on
a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with species
set $S$ and finite reaction set $\rho$, with propensities
$\lambda_r \colon \mathbb{N}^S \to [0, \infty)$, and for each reaction $r$ let
$y_r \colon [0, \infty) \to \mathbb{N}$ be a function (in the intended use, the path of a unit-rate
counting process). A count path $X \colon \mathbb{R} \to \mathbb{N}^S$ satisfies the random
time-change equations of $C$ driven by the $y_r$ (Kurtz's representation; Ethier–Kurtz 1986, ch. 6,
(4.1); Anderson–Kurtz 2015) if each coordinate $t \mapsto X(t)_i$ is measurable, if for every
reaction $r$ and every real $t$, negative values included, the function $s \mapsto \lambda_r(X(s))$
is integrable on the interval between $0$ and $t$, and if for every $t \ge 0$ and every species $i$,
in the real numbers,

$$X(t)_i = X(0)_i + \sum_{r \in \rho} y_r(\tau_r(t))\, \zeta_r(i),$$

where $\tau_r(t) = \max\left(0, \int_0^t \lambda_r(X(s))\, ds\right)$ is the
[internal clock](clock.md) of $r$ and $\zeta_r = \mathrm{prod}(r) - \mathrm{src}(r)$ its
[reaction vector](reaction-vector.md).

Nothing is required of the $y_r$ beyond these equations, and nothing of $X$ at negative times beyond
measurability and integrability. These two conditions make the clocks Lebesgue integrals of the
propensities; a càdlàg path is measurable, and along a non-explosive path the propensities are
locally bounded on $[0, \infty)$. In the intended use the $y_r$ are the paths of independent
unit-rate
[Poisson processes](../../../Probability/point-processes/poisson-processes/is-poisson-process.md)
and the initial state $X(0)$ is independent of them; a process almost all of whose paths satisfy
these equations is then the continuous-time Markov chain in which reaction $r$ fires at rate
$\lambda_r(X)$ and moves the state by $\zeta_r$.
