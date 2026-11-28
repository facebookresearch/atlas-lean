# Bounded diameters of the cells

Let $(X_{h,i}, x_{h,i})$ be a [hierarchical partition](hierarchical-partition.md) of a set $\mathcal X$ and $\ell$ a
[semi-metric](semi-metric.md) on $\mathcal X$. A function $\delta \colon \mathbb{N} \to \mathbb{R}$ *bounds the diameters
of the cells* if $\delta(h) > 0$ and $\delta(h + 1) \le \delta(h)$ for every $h \ge 0$, and

$$
\ell(x_{h,i}, x) \le \delta(h) \quad \text{for every node } (h, i) \text{ and every } x \in X_{h,i}.
$$

The sources ask for a decreasing sequence; only $\delta(h + 1) \le \delta(h)$ is used, so $\delta$ need not decrease
strictly. They write the bound as $\sup_{x \in X_{h,i}} \ell(x_{h,i}, x) \le \delta(h)$, which is the same condition.

For example, for the half-open dyadic intervals of $[0, 1)$ with their midpoints and $\ell(x, y) = |x - y|$, the
function $\delta(h) = 2^{-h-1}$ bounds the diameters of the cells.

## Sources

- R. Munos, *Optimistic optimization of a deterministic function without the knowledge of its smoothness*, Advances
  in Neural Information Processing Systems 24 (NeurIPS 2011), Assumption 3 ("bounded diameters").
- R. Munos, *From Bandits to Monte-Carlo Tree Search: The Optimistic Principle Applied to Optimization and Planning*,
  Foundations and Trends in Machine Learning 7(1), 2014, 1–129 (HAL hal-00747575v5,
  <https://hal.science/hal-00747575v5>), Section 3.2.2, Assumption 3 ("decreasing diameters").

## Depends on

- [Hierarchical partition](hierarchical-partition.md)
- [Semi-metric](semi-metric.md)
