# Planar first-passage metric and time constant

Index the independent passage weights by the unoriented nearest-neighbor edges of $\mathbb Z^2$. For two vertices the passage time is the infimum of weight sums of finite lattice paths between them, including the length-zero path on the diagonal. In a direction $v\in\mathbb R^2$ use the lattice vertex obtained by coordinatewise integer floor of $tv$. The time-constant condition is that, for every fixed $v$, for almost every environment the passage time from zero to that vertex divided by $t$ tends to the specified real $\mu(v)$ as $t\to+\infty$ through the reals. Here $\mu$ is required to be a norm: positivity away from zero, triangle inequality, and homogeneity with $|a|$ for real scalars $a$. Its unit sublevel set is the limit shape. The Gamma and exponential edge laws are distinct inputs in the respective statements, not directed growth models.

## Sources

- [Pinned source definition](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/GammaPassage.lean#L13-L100)
- [Pinned model definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/PlanarFirstPassage.lean#L18-L89)
