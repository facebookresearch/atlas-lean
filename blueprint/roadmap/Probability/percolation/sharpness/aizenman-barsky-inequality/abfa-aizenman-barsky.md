# Aizenman–Barsky inequality on a finite graph

Let $G$ be a graph on a finite vertex set $V$, $o \in V$, $J$ a real function on unordered pairs of elements of $V$ with $J_e \ge 0$ for every edge $e$ of $G$, and $J_0 \in \mathbb{R}$ such that the [incident coupling](abcr-incident-coupling.md) $\sum_{y \sim x} J_{xy}$ equals $J_0$ for every $x \in V$. Let $\beta, h \ge 0$ and let $M(\beta, h)$ be the [finite-volume percolation magnetization](abfa-mag.md) at $o$. Assume that at $(\beta, h)$ every site has the same magnetization: the probability that $x$ is connected to the ghost equals $M(\beta, h)$ for every $x \in V$. Then

$$\partial_\beta M(\beta, h) \le J_0\, M(\beta, h)\, \partial_h M(\beta, h),$$

with a derivative read as $0$ where the function is not differentiable.

## Sources

- Michael Aizenman and David J. Barsky, *Sharpness of the phase transition in percolation models*, Comm. Math. Phys. 108
  (1987), no. 3, 489–526, DOI 10.1007/bf01212322.
