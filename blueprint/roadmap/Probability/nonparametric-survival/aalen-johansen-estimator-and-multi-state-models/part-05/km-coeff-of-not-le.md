# Kaplan–Meier influence coefficient vanishes beyond the evaluation index

Let $k$ and $r$ be natural numbers; grid indices range over $\{0, \dots, k-1\}$ and causes over $\{0, \dots, r-1\}$. A cell vector is an element $u$ of the Euclidean space $\mathbb{R}^{\mathrm{Cell}_{k,r}}$ indexed by the [cells](../part-01/cell.md); write $u^{E}_{l,c}$ for its coordinate at the event cell $(l, c)$ and $u^{R}_{l}$ for its coordinate at the at-risk cell $l$.

The Kaplan–Meier factor of $u$ at grid index $i$ is

$$f_i(u) = 1 - \frac{\sum_{c=0}^{r-1} u^{E}_{i,c}}{u^{R}_{i}},$$

with real division, $x/0 = 0$.

For grid indices $j$ and $l$, the [Kaplan–Meier influence coefficient](km-coeff.md) is

$$\kappa_j(u; l) = \begin{cases} -\dfrac{\prod_{i \le j,\, i \ne l} f_i(u)}{u^{R}_{l}} & \text{if } l \le j, \\ 0 & \text{otherwise,} \end{cases}$$

with $x/0 = 0$.

For every cell vector $u$ and all grid indices $j$ and $l$ with $l > j$,

$$\kappa_j(u; l) = 0.$$
