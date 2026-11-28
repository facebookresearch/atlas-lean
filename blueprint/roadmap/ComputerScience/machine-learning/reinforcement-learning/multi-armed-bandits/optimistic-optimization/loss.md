# Loss of a returned point

Let $f \colon \mathcal X \to \mathbb{R}$ attain its maximum $f^* = \max_{\mathcal X} f$. The *loss* of a point
$x \in \mathcal X$ is $f^* - f(x) \ge 0$. An optimization algorithm that evaluates $f$ at points it chooses and returns a
point $x(n)$ after a budget $n$ has *loss* $r_n = f^* - f(x(n))$.

For the algorithms of the [deterministic case](deterministic/README.md), $n$ counts the expansions of nodes of a
[hierarchical partition](hierarchical-partition.md); each expansion evaluates $f$ at $K$ new centers. The loss, also
called simple regret, measures the returned point only, unlike the cumulative regret
$n f^* - \sum_{t=1}^n f(x_t)$ of the evaluated points $x_1, \dots, x_n$.

The sources define $r_n = \sup_{\mathcal X} f - f(x(n))$; when $f$ attains its maximum, as under
[local smoothness around a maximizer](local-smoothness-around-a-maximizer.md), the supremum is the maximum.

## Sources

- R. Munos, *Optimistic optimization of a deterministic function without the knowledge of its smoothness*, Advances
  in Neural Information Processing Systems 24 (NeurIPS 2011), Section 1, equation (1).
- R. Munos, *From Bandits to Monte-Carlo Tree Search: The Optimistic Principle Applied to Optimization and Planning*,
  Foundations and Trends in Machine Learning 7(1), 2014, 1–129 (HAL hal-00747575v5,
  <https://hal.science/hal-00747575v5>), Chapter 3, equations (3.1) and (3.2), and Remark 3.4.
