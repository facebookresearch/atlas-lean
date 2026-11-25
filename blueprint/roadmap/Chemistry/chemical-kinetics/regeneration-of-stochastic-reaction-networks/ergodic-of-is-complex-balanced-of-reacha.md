# Positive complex balance, drift bound and reachability give ergodicity

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

Then, for the jump–hold chain with jump chain $Y$, [jump times](../non-explosion-of-stochastic-reaction-networks/jump-time-2.md) $T_n$
and path $X$:

- the chain started at $x_0$ returns to $x_0$ almost surely: $Y_n = x_0$ for some $n \ge 1$;
- the mean return time is finite: for the chain started at $x_0$, the time $T_{\tau_1}$ of the
  first return, where $\tau_1$ is the first $n \ge 1$ with $Y_n = x_0$ ($T_{\tau_1} = 0$ if
  there is none), is integrable;
- for every initial state $x$ and every $f : \mathbb{N}^S \to \mathbb{R}$ with $|f(y)| \le B$
  for every $y$ (some real $B$), almost surely

$$\frac{1}{t} \int_0^t f(X^x_s)\, ds \to \sum_{y \in \mathbb{N}^S} \pi_c(y)\, f(y) \quad
(t \to \infty),$$

where the [product-form Poisson weights](../../../Biology/systems-biology/stochastic-mass-action-metabolic-control-and-flu/poisson-weight.md)
$\pi_c(x) = \prod_{s \in S} c_s^{x_s} e^{-c_s} / x_s!$ (with $0^0 = 1$) form a probability law on
$\mathbb{N}^S$. The integral is the [occupation integral](../ergodic-theorem-for-complex-balanced-reaction-ne/occupation.md) of $f$.
A return may be a jump $x_0 \to x_0$ by a reaction with $\mathrm{src}(r) = \mathrm{prod}(r)$.

The [ergodic theorem for a general path process](../ergodic-theorem-for-complex-balanced-reaction-ne/ergodic-of-is-complex-balanced.md)
assumes non-explosion, the stationarity of $\pi_c$ and regeneration at $x_0$; for the jump–hold
chain they are replaced here by the drift bound and reachability from $x_0$.
