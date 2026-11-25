# Razborov's triangle density function

The function $h$ of an edge density $a$ with $h(a) = 0$ for $a \le 1/2$, $h(a) = 1$ for $a \ge 1$, and, for $1 - 1/t < a \le 1 - 1/(t+1)$ with $t \ge 2$ (so that $t = \lceil 1/(1-a) \rceil - 1$),

$$h(a) = 6\left(\binom{t}{3}c^3 + \binom{t}{2}c^2(1 - tc)\right), \qquad c = \frac{t + \sqrt{t(t - a(t+1))}}{t(t+1)}.$$

It is the triangle density of the complete $(t+1)$-partite graph with edge density $a$ whose $t$ largest parts have equal relative size $c$ (the last part has size $1 - tc$). [Razborov's minimum triangle density theorem](razborov-minimum-triangle-density.md) states that no graph sequence of edge density $a$ has asymptotically fewer triangles. At the Turán densities $h$ [equals $t(t-1)/(t+1)^2$](razborov-triangle-density-one-sub-inv.md).

## Sources

- O. Pikhurko and A. Razborov, Asymptotic structure of graphs with the minimum number of triangles, Combin. Probab. Comput. 26 (2017), arXiv:1204.2846v2, equations (1)-(4).
- A. A. Razborov, On the minimal density of triangles in graphs, Combin. Probab. Comput. 17 (2008), 603-618.
