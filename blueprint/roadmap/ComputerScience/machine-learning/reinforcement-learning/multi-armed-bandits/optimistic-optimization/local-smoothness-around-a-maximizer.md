# Local smoothness around a maximizer

Let $\ell$ be a [semi-metric](semi-metric.md) on a set $\mathcal X$. A function $f \colon \mathcal X \to \mathbb{R}$ is
*locally smooth around a maximizer* with respect to $\ell$ if there is a point $x^* \in \mathcal X$ such that, for every
$x \in \mathcal X$, $f(x) \le f(x^*)$ and

$$
f(x^*) - f(x) \le \ell(x, x^*).
$$

Then $f$ attains its maximum $f^* = f(x^*) = \max_{\mathcal X} f$. The condition is a one-sided Lipschitz condition at
$x^*$ only: it bounds how fast $f$ decreases near $x^*$, and $f$ may be discontinuous elsewhere.

## Sources

- R. Munos, *Optimistic optimization of a deterministic function without the knowledge of its smoothness*, Advances
  in Neural Information Processing Systems 24 (NeurIPS 2011), Assumption 2.
- R. Munos, *From Bandits to Monte-Carlo Tree Search: The Optimistic Principle Applied to Optimization and Planning*,
  Foundations and Trends in Machine Learning 7(1), 2014, 1–129 (HAL hal-00747575v5,
  <https://hal.science/hal-00747575v5>), Section 3.2.2, Assumption 2 and Figure 3.5.

## Depends on

- [Semi-metric](semi-metric.md)
