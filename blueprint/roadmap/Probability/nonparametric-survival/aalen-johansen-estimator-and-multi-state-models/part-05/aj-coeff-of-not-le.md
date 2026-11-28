# Aalen–Johansen influence coefficient vanishes beyond the evaluation index

Let $k$ and $r$ be natural numbers; grid indices range over $\{0, \dots, k-1\}$ and causes over $\{0, \dots, r-1\}$. A cell vector is an element $u$ of the Euclidean space $\mathbb{R}^{\mathrm{Cell}_{k,r}}$ indexed by the [cells](../part-01/cell.md); write $u^{E}_{l,c}$ for its coordinate at the event cell $(l, c)$ and $u^{R}_{l}$ for its coordinate at the at-risk cell $l$.

The Kaplan–Meier factor of $u$ at grid index $i$ is

$$f_i(u) = 1 - \frac{\sum_{c=0}^{r-1} u^{E}_{i,c}}{u^{R}_{i}},$$

with real division, $x/0 = 0$.

For grid indices $j, l$ and causes $c, c'$, the [Aalen–Johansen influence coefficient](../part-01/aj-coeff.md) of the cause-$c'$ increment at $l$ for the cumulative incidence of cause $c$ at $j$ is

$$a_{j,c}(u; l, c') = \frac{[\,l \le j \text{ and } c' = c\,] \prod_{i < l} f_i(u)}{u^{R}_{l}} - \frac{\sum_{l < l' \le j} \big(\prod_{i < l',\, i \ne l} f_i(u)\big)\, u^{E}_{l',c} / u^{R}_{l'}}{u^{R}_{l}},$$

where $[\cdot]$ is $1$ when the condition holds and $0$ otherwise, every quotient uses $x/0 = 0$, empty products are $1$ and empty sums are $0$.

For every cell vector $u$, all grid indices $j$ and $l$ with $l > j$, and all causes $c$ and $c'$,

$$a_{j,c}(u; l, c') = 0.$$
