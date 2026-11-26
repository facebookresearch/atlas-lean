# Derivative of a cause-specific ratio along a line of cell vectors

Let $k$ and $r$ be natural numbers; grid indices range over $\{0, \dots, k-1\}$ and causes over $\{0, \dots, r-1\}$. A cell vector is an element $u$ of the Euclidean space $\mathbb{R}^{\mathrm{Cell}_{k,r}}$ indexed by the [cells](cell.md); write $u^{E}_{l,c}$ for its coordinate at the event cell $(l, c)$ and $u^{R}_{l}$ for its coordinate at the at-risk cell $l$.

For cell vectors $u, v$, a grid index $l$ and a cause $c$, the cause-$c$ increment of $v$ centred by the ratios of $u$ is

$$\Delta_{l,c}(u, v) = v^{E}_{l,c} - \frac{u^{E}_{l,c}}{u^{R}_{l}}\, v^{R}_{l},$$

with real division, $x/0 = 0$.

For every cell vector $u$ and grid index $l$ with $u^{R}_{l} \ne 0$, every cell vector $v$ and every cause $c$, the function

$$t \mapsto \frac{u^{E}_{l,c} + t\, v^{E}_{l,c}}{u^{R}_{l} + t\, v^{R}_{l}}$$

on $\mathbb{R}$ (real division, $x/0 = 0$) has derivative $\Delta_{l,c}(u, v) / u^{R}_{l}$ at $t = 0$.
