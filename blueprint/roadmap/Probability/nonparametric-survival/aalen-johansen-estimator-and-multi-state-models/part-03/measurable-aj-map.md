# Measurability of the Aalen–Johansen map

Let $k$ and $r$ be natural numbers; grid indices range over $\{0, \dots, k-1\}$ and causes over $\{0, \dots, r-1\}$. A cell vector is an element $u$ of the Euclidean space $\mathbb{R}^{\mathrm{Cell}_{k,r}}$ indexed by the [cells](../part-01/cell.md); write $u^{E}_{l,c}$ for its coordinate at the event cell $(l, c)$ and $u^{R}_{l}$ for its coordinate at the at-risk cell $l$.

The Kaplan–Meier factor of $u$ at grid index $i$ is

$$f_i(u) = 1 - \frac{\sum_{c=0}^{r-1} u^{E}_{i,c}}{u^{R}_{i}},$$

with real division, $x/0 = 0$.

For a horizon $m \in \{0, \dots, k-1\}$, the Aalen–Johansen map $A_m$ sends a cell vector $u$ to the real vector indexed by the [coordinates](../part-02/coord.md) $(\star, j)$ and $(c, j)$, $j \le m$, $c$ a cause, given by

$$A_m(u)_{(\star, j)} = \prod_{l \le j} f_l(u), \qquad A_m(u)_{(c, j)} = \sum_{l \le j} \Big(\prod_{i < l} f_i(u)\Big) \frac{u^{E}_{l,c}}{u^{R}_{l}},$$

with real division, $x/0 = 0$, empty products equal to $1$, and indices $i, l$ ranging over grid indices.

For every horizon $m \in \{0, \dots, k-1\}$, the map $u \mapsto A_m(u)$ from $\mathbb{R}^{\mathrm{Cell}_{k,r}}$ to $\mathbb{R}^{\mathrm{Coord}_{k,r}(m)}$ is measurable, for the Borel $\sigma$-algebra on the space of cell vectors and the product of the Borel $\sigma$-algebras on $\mathbb{R}^{\mathrm{Coord}_{k,r}(m)}$.
