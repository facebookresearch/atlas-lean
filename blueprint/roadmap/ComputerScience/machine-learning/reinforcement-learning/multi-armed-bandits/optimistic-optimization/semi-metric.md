# Semi-metric

A *semi-metric* on a set $\mathcal X$ is a function $\ell \colon \mathcal X \times \mathcal X \to [0, \infty)$ such that,
for all $x, y \in \mathcal X$, $\ell(x, y) = \ell(y, x)$, and $\ell(x, y) = 0$ if and only if $x = y$. It need not
satisfy the triangle inequality. For $x \in \mathcal X$ and $r > 0$, the *$\ell$-ball* of radius $r$ centered at $x$ is

$$
B_\ell(x, r) = \{y \in \mathcal X : \ell(x, y) < r\};
$$

it contains $x$.

For a norm on $\mathbb{R}^D$ and $\alpha > 0$, $\ell(x, y) = \|x - y\|^\alpha$ is a semi-metric on $\mathbb{R}^D$; it is a
metric when $\alpha \le 1$, and fails the triangle inequality when $\alpha > 1$.

The sources do not say whether balls are open or closed; balls are open here, so that partitions into half-open cells,
such as those of the sources' examples, have well-shaped cells with constant $\nu = 1$.

## Sources

- R. Munos, *Optimistic optimization of a deterministic function without the knowledge of its smoothness*, Advances
  in Neural Information Processing Systems 24 (NeurIPS 2011), Assumption 1.
- R. Munos, *From Bandits to Monte-Carlo Tree Search: The Optimistic Principle Applied to Optimization and Planning*,
  Foundations and Trends in Machine Learning 7(1), 2014, 1–129 (HAL hal-00747575v5,
  <https://hal.science/hal-00747575v5>), Section 3.2.2, Assumption 1.
