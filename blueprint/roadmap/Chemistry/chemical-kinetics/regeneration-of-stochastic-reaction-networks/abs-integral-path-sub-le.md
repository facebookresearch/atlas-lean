# Occupation integrals of bounded observables are Lipschitz in time

Let $\sigma$ be a countable set of states whose σ-algebra contains the singletons,
$q : \sigma \to \mathbb{R}$ any rates, $x \in \sigma$, and $\omega$ a sequence of steps such that
the [path](../non-explosion-of-stochastic-reaction-networks/path.md) $s \mapsto X_s$ of the chain
started at $x$ is measurable; nothing else is assumed about the rates or the clocks. Let
$g : \sigma \to \mathbb{R}$ satisfy $|g(y)| \le B$ for every $y$. Then for all real $s \le t$,

$$\left| \int_0^t g(X_u)\, du - \int_0^s g(X_u)\, du \right| \le B\, (t - s) .$$

The integrals are oriented ($\int_0^s = -\int_s^0$ for $s < 0$), and the difference is
$\int_s^t g(X_u)\, du$, whose integrand is bounded by $B$. So $t \mapsto \int_0^t g(X_u)\, du$ is
Lipschitz with constant $B$.
