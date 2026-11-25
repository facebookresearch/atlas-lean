# Complex balance and a drift bound give stationarity in Laplace form

Let $N$ be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with finite sets $S$ of species and
$\rho$ of reactions, $\kappa \in \mathbb{R}^\rho$ with $\kappa_r \ge 0$ for every $r$, and
$c \in \mathbb{R}^S$ with $c_s \ge 0$ for every $s$ that is
[complex balanced](../../../Biology/systems-biology/complex-balancing-and-the-deficiency-zero-theore/is-complex-balanced.md) for $\kappa$. Let $\lambda_r$ be the
[mass-action propensities](../../../Biology/systems-biology/stochastic-mass-action-metabolic-control-and-flu/propensity.md) and consider the
[stochastic mass-action network](mass-action.md) of $N$ and $\kappa$, with
[generator](../non-explosion-of-stochastic-reaction-networks/generator.md)
$L V(x) = \sum_r \lambda_r(x) \bigl(V(x - \mathrm{src}(r) + \mathrm{prod}(r)) - V(x)\bigr)$,
[law of the steps](../non-explosion-of-stochastic-reaction-networks/input-measure-2.md) $\mathbb{P}$ and
[path](../non-explosion-of-stochastic-reaction-networks/path-2.md) $X^x$ from the state $x$. Let
$V : \mathbb{N}^S \to [0, \infty)$ and $a, b \ge 0$ satisfy the drift bound
$L V(x) \le a V(x) + b$ and $\sum_s x_s \le V(x)$ for every $x \in \mathbb{N}^S$; by the
[Foster–Lyapunov criterion](../non-explosion-of-stochastic-reaction-networks/ae-tendsto-jump-time-at-top-of-coercive.md) the chain
then does not explode from any state.

Then for every $g : \mathbb{N}^S \to \mathbb{R}$ with $0 \le g \le 1$ and every $\theta > 0$, with
the [product-form Poisson weights](../../../Biology/systems-biology/stochastic-mass-action-metabolic-control-and-flu/poisson-weight.md)
$\pi_c(x) = \prod_{s \in S} c_s^{x_s} e^{-c_s} / x_s!$ (with $0^0 = 1$),

$$\sum_{x \in \mathbb{N}^S} \pi_c(x)\, \mathbb{E}\Bigl[\int_0^\infty \theta e^{-\theta t}\,
g(X^x_t)\, dt\Bigr] = \sum_{x \in \mathbb{N}^S} \pi_c(x)\, g(x),$$

where the expectation and the integral over $t > 0$ are integrals of nonnegative functions
(lower integrals, with values in $[0, \infty]$) and the sums are taken in $[0, \infty]$. It is the
Laplace form of the stationarity of $\pi_c$: for $g$ the indicator of a state $y$ the right side
is $\pi_c(y) = \int_0^\infty \theta e^{-\theta t} \pi_c(y)\, dt$. The fixed-time identity, that
the chain started from $\pi_c$ is at $y$ at time $t$ with probability $\pi_c(y)$, is the
forward-equation step that the
[ergodic theorem for a general path process](../ergodic-theorem-for-complex-balanced-reaction-ne/ergodic-of-is-complex-balanced.md)
assumes; it is not part of this statement.
