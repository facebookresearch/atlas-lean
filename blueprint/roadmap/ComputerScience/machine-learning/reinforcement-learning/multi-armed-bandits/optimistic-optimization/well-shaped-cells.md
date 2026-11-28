# Well-shaped cells

Let $(X_{h,i}, x_{h,i})$ be a [hierarchical partition](hierarchical-partition.md) of a set $\mathcal X$, $\ell$ a
[semi-metric](semi-metric.md) on $\mathcal X$, and $\delta \colon \mathbb{N} \to \mathbb{R}$ a function with
$\delta(h) > 0$ for every $h$. The cells are *well shaped* for $\ell$ and $\delta$ with constant $\nu > 0$ if every
cell contains the $\ell$-ball of radius $\nu \delta(h)$ centered at its center:

$$
B_\ell(x_{h,i}, \nu \delta(h)) \subseteq X_{h,i} \quad \text{for every node } (h, i).
$$

In the sources $\delta$ is a function that [bounds the diameters of the cells](bounded-diameters.md); that property is
not needed to state this one. As the cells of a given depth are pairwise disjoint, so are the balls
$B_\ell(x_{h,i}, \nu \delta(h))$ of that depth.

For example, for the half-open dyadic intervals of $[0, 1)$ with their midpoints, $\ell(x, y) = |x - y|$ and
$\delta(h) = 2^{-h-1}$, the cells are well shaped with constant $\nu = 1$.

## Sources

- R. Munos, *Optimistic optimization of a deterministic function without the knowledge of its smoothness*, Advances
  in Neural Information Processing Systems 24 (NeurIPS 2011), Assumption 4.
- R. Munos, *From Bandits to Monte-Carlo Tree Search: The Optimistic Principle Applied to Optimization and Planning*,
  Foundations and Trends in Machine Learning 7(1), 2014, 1–129 (HAL hal-00747575v5,
  <https://hal.science/hal-00747575v5>), Section 3.2.2, Assumption 4.

## Depends on

- [Hierarchical partition](hierarchical-partition.md)
- [Semi-metric](semi-metric.md)
