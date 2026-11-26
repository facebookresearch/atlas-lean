# Aizenman–Barsky inequality on $\mathbb{Z}^d$

Let $d \in \mathbb{N}$ and let $J$ be a function on unordered pairs of sites of $\mathbb{Z}^d$ with $J \ge 0$, $J_{xy} = 0$ unless $x$ and $y$ are nearest neighbours, and $J$ translation invariant: $J_{u + x, v + x} = J_{uv}$ for all $x, u, v$. Assume $|J| = \sum_{y \in \mathbb{Z}^d} J_{0y}$ converges. Then the [infinite-volume percolation magnetization](abig-mag.md) $M(\beta, h)$ at the origin, for independent bond percolation on $\mathbb{Z}^d$ with edge probabilities $1 - e^{-\beta J_e}$ and a ghost field with ghost-edge probability $1 - e^{-h}$, satisfies the first Aizenman–Barsky differential inequality

$$\partial_\beta M(\beta, h) \le |J|\, M(\beta, h)\, \partial_h M(\beta, h) \quad \text{for all } \beta \ge 0,\ h > 0.$$

A derivative is read as $0$ where the function is not differentiable, so the inequality is trivial at points where $\beta \mapsto M(\beta, h)$ is not differentiable. Aizenman and Barsky allow general summable translation-invariant couplings, whereas the coupling $J$ above vanishes off lattice edges. The [second Aizenman–Barsky inequality](aizenman-barsky-pdi.md) is a separate statement.

## Sources

- Michael Aizenman and David J. Barsky, *Sharpness of the phase transition in percolation models*, Comm. Math. Phys. 108
  (1987), no. 3, 489–526, DOI 10.1007/bf01212322.
