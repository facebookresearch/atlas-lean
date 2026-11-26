# Cause-specific coordinate of the Aalen–Johansen map as a cumulative incidence

Let $k$ and $r$ be natural numbers; grid indices range over $\{0, \dots, k-1\}$ and causes over $\{0, \dots, r-1\}$. A cell vector is an element $u$ of the Euclidean space $\mathbb{R}^{\mathrm{Cell}_{k,r}}$ indexed by the [cells](../part-01/cell.md); write $u^{E}_{l,c}$ for its coordinate at the event cell $(l, c)$ and $u^{R}_{l}$ for its coordinate at the at-risk cell $l$.

The Kaplan–Meier factor of $u$ at grid index $i$ is

$$f_i(u) = 1 - \frac{\sum_{c=0}^{r-1} u^{E}_{i,c}}{u^{R}_{i}},$$

with real division, $x/0 = 0$.

The product-limit survival just before grid index $l$ and the cumulative incidence of cause $c$ at grid index $j$ are

$$S_l(u) = \prod_{i < l} f_i(u), \qquad F_c(u; j) = \sum_{l \le j} S_l(u)\, \frac{u^{E}_{l,c}}{u^{R}_{l}},$$

with $x/0 = 0$, an empty product equal to $1$, and indices ranging over grid indices; $F_c(u; j)$ is defined at every grid index $j$.

For a horizon $m \in \{0, \dots, k-1\}$, the [Aalen–Johansen map](../part-01/aj-map.md) $A_m$ sends a cell vector to a real vector indexed by the [coordinates](../part-02/coord.md) $(\star, j)$ and $(c, j)$ with $j \le m$ and $c$ a cause.

For every horizon $m$, every cell vector $u$, every cause $c$ and every grid index $j \le m$,

$$A_m(u)_{(c, j)} = F_c(u; j).$$
