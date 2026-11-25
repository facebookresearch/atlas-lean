# First-step equation of the mean Abel functional for $q > 0$, $a \ge 0$

Let $\sigma$ be a countable set of states whose σ-algebra contains the singletons (so every
subset of $\sigma$ is measurable), and let $K$ be a jump kernel on $\sigma$: a probability mass
function $K(y, \cdot)$ on $\sigma$ for each state $y$. Under the
[law of the step sequence](../non-explosion-of-stochastic-reaction-networks/input-measure.md)
$\mathbb{P}$, a probability measure, the steps $(\xi_k, E_k)$, $k \in \mathbb{N}$, are i.i.d.:
$\xi_k : \sigma \to \sigma$ has independent coordinates $\xi_k(y) \sim K(y, \cdot)$, and $E_k$ is
an independent exponential clock of rate $1$. Let $q : \sigma \to \mathbb{R}$ be positive rates
($q(y) > 0$ for every $y$), $g : \sigma \to \mathbb{R}$ any observable and $a \ge 0$, and let

$$\mathbb{E}_y[A] = \int A_a g(y, \omega)\, d\mathbb{P}(\omega) \in [0, \infty]$$

be the expected [Abel functional](abel-sum.md) of the chain started at $y$, a lower Lebesgue
integral. Then for every state $x$,

$$
\mathbb{E}_x[A] = g(x)^+ \frac{a}{q(x) + a} + \frac{q(x)}{q(x) + a} \sum_{y \in \sigma} K(x, y)\,
\mathbb{E}_y[A],
$$

an identity in $[0, \infty]$ (with $0 \cdot \infty = 0$), where $g(x)^+ = \max(g(x), 0)$. This is
the resolvent equation of the chain. The first holding time $E_0 / q(x)$ has Laplace transform
$\mathbb{E}\bigl[e^{-a E_0 / q(x)}\bigr] = q(x) / (q(x) + a)$, the first jump goes to a state of
law $K(x, \cdot)$, and the chain then restarts with steps that are independent of the first step
and have the law $\mathbb{P}$ again.
