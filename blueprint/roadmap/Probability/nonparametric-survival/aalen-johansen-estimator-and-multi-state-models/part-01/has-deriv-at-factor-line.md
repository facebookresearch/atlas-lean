# Derivative of a Kaplan–Meier factor along a line of cell vectors

Let $k$ and $r$ be natural numbers; grid indices range over $\{0, \dots, k-1\}$ and causes over $\{0, \dots, r-1\}$. A cell vector is an element $u$ of the Euclidean space $\mathbb{R}^{\mathrm{Cell}_{k,r}}$ indexed by the [cells](cell.md); write $u^{E}_{l,c}$ for its coordinate at the event cell $(l, c)$ and $u^{R}_{l}$ for its coordinate at the at-risk cell $l$.

The Kaplan–Meier factor of $u$ at grid index $i$ is

$$f_i(u) = 1 - \frac{\sum_{c=0}^{r-1} u^{E}_{i,c}}{u^{R}_{i}},$$

with real division, $x/0 = 0$.

For cell vectors $u, v$, a grid index $l$ and a cause $c$, the cause-$c$ increment of $v$ centred by the ratios of $u$ is

$$\Delta_{l,c}(u, v) = v^{E}_{l,c} - \frac{u^{E}_{l,c}}{u^{R}_{l}}\, v^{R}_{l}.$$

For every cell vector $u$ and grid index $l$ with $u^{R}_{l} \ne 0$, and every cell vector $v$, the function $t \mapsto f_l(u + t v)$ on $\mathbb{R}$ has derivative

$$-\frac{\sum_{c=0}^{r-1} \Delta_{l,c}(u, v)}{u^{R}_{l}}$$

at $t = 0$.
