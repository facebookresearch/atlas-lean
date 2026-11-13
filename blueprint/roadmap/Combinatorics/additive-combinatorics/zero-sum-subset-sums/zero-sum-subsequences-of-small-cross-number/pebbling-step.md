# Lagarias–Saks pebbling step

Let $G$ be a simple graph on a vertex set $V$, and let $w$
assign a natural-number cost $w(uv)$ to each unordered pair of vertices $\{u, v\}$. For
configurations $C, C' : V \to \mathbb{N}$, there is a pebbling step from $C$ to $C'$ if there
is an edge $uv$ of $G$ with $0 < w(uv) \le C(u)$ such that $C'$ is obtained from $C$ by
removing $w(uv)$ pebbles from $u$ and adding one pebble to $v$.

Each edge has one cost, used in both directions. The source's costs are positive, and the step
requires $w(uv) > 0$, so a zero cost never creates a pebble for free.

## Sources

- Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in Abelian Groups*, INTEGERS 24 (2024), Article A93, Section 2.2 (pebbling step).
