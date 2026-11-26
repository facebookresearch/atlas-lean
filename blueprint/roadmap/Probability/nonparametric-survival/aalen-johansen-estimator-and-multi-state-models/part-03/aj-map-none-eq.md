# Survival coordinate of the Aalen–Johansen map as a product of Kaplan–Meier factors

Let $k$ and $r$ be natural numbers; grid indices range over $\{0, \dots, k-1\}$ and causes over $\{0, \dots, r-1\}$. A cell vector is an element $u$ of the Euclidean space $\mathbb{R}^{\mathrm{Cell}_{k,r}}$ indexed by the [cells](../part-01/cell.md); write $u^{E}_{l,c}$ for its coordinate at the event cell $(l, c)$ and $u^{R}_{l}$ for its coordinate at the at-risk cell $l$.

The Kaplan–Meier factor of $u$ at grid index $i$ is

$$f_i(u) = 1 - \frac{\sum_{c=0}^{r-1} u^{E}_{i,c}}{u^{R}_{i}},$$

with real division, $x/0 = 0$.

For a horizon $m \in \{0, \dots, k-1\}$, the [Aalen–Johansen map](../part-01/aj-map.md) $A_m$ sends a cell vector to a real vector indexed by the [coordinates](../part-02/coord.md) $(\star, j)$ and $(c, j)$ with $j \le m$ and $c$ a cause.

For every horizon $m$, every cell vector $u$ and every grid index $j \le m$, the survival coordinate is the product of the Kaplan–Meier factors up to $j$:

$$A_m(u)_{(\star, j)} = \prod_{i \le j} f_i(u),$$

the product running over grid indices $i$.
