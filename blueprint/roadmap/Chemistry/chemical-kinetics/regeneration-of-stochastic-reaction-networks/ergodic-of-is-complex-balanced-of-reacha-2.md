# Complex-balanced Poisson start, drift bound, reachability: ergodicity

Let $N$ be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with finite sets $S$ of species and
$\rho$ of reactions, $\kappa \in \mathbb{R}^\rho$ with $\kappa_r \ge 0$ for every $r$, and
$c \in \mathbb{R}^S$ with $c_s > 0$ for every $s$ that is
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
Let $x_0 \in \mathbb{N}^S$ be a state from which every state $y$ is reachable along reactions
with positive propensity: there are states $x_0 = u_0, u_1, \dots, u_m = y$ ($m \ge 0$) and
reactions $r_1, \dots, r_m$ with $\lambda_{r_i}(u_{i-1}) > 0$ and
$u_i = u_{i-1} - \mathrm{src}(r_i) + \mathrm{prod}(r_i)$ for every $i$.

Let the [product-form Poisson weights](../../../Biology/systems-biology/stochastic-mass-action-metabolic-control-and-flu/poisson-weight.md)
$\pi_c(x) = \prod_{s \in S} c_s^{x_s} e^{-c_s} / x_s!$ (with $0^0 = 1$), a probability law on
$\mathbb{N}^S$, and let the initial state $z$ be drawn from $\pi_c$ (the
[law with mass function](../ergodic-theorem-for-complex-balanced-reaction-ne/count-law.md) $\pi_c$) independently of the steps: the pair
$(z, \omega)$ has law $\pi_c \otimes \mathbb{P}$. Then for every $f : \mathbb{N}^S \to \mathbb{R}$
with $|f(y)| \le B$ for every $y$ (some real $B$), for $\pi_c \otimes \mathbb{P}$-almost every
$(z, \omega)$

$$\frac{1}{t} \int_0^t f(X^z_s(\omega))\, ds \to \sum_{y \in \mathbb{N}^S} \pi_c(y)\, f(y)
\quad (t \to \infty).$$

This is the conclusion of the
[ergodic theorem for a general path process](../ergodic-theorem-for-complex-balanced-reaction-ne/ergodic-of-is-complex-balanced.md),
for the jump–hold chain started from $\pi_c$, with its assumptions of non-explosion, of the
stationarity of $\pi_c$ and of regeneration replaced by the drift bound and reachability.
