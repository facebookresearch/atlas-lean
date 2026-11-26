# Aizenman–Barsky inequality on countable vertex-transitive graphs

Let $G$ be a graph on a countable vertex set $V$, $o \in V$, $J$ a function on unordered pairs of elements of $V$ and $J_0 \ge 0$. Assume:

- $J \ge 0$, and $J_{xy} = 0$ whenever $x$ and $y$ are not adjacent in $G$;
- for every $x$, the row sum $\sum_{y \sim x} J_{xy}$ converges and is at most $J_0$;
- (transitivity) for every $x \in V$ there is a permutation $\tau_x$ of $V$ with $\tau_x(o) = x$ that preserves adjacency in $G$ and the coupling: $J_{\tau_x(u) \tau_x(v)} = J_{uv}$ for all $u, v$;
- there are finite sets $S_0, S_1, \dots \subseteq V$ containing $o$ whose [ghost windows](abig-ghost-window.md) $S_n \cup \{\mathfrak{g}\}$ increase with $n$ and eventually contain every finite subset of $V \cup \{\mathfrak{g}\}$.

Then the [infinite-volume percolation magnetization](abig-mag.md) $M$ at $o$ satisfies the [Aizenman–Barsky inequality for $\beta \ge 0$ and $h > 0$](aizenman-barsky-inequality-physical.md) with constant $J_0$:

$$\partial_\beta M(\beta, h) \le J_0\, M(\beta, h)\, \partial_h M(\beta, h) \quad \text{for all } \beta \ge 0,\ h > 0.$$

## Sources

- Michael Aizenman and David J. Barsky, *Sharpness of the phase transition in percolation models*, Comm. Math. Phys. 108
  (1987), no. 3, 489–526, DOI 10.1007/bf01212322.
