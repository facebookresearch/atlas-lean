# Coordinates of the derivative of the Aalen–Johansen map from derivatives along lines

Let $k$ and $r$ be natural numbers; grid indices range over $\{0, \dots, k-1\}$ and causes over $\{0, \dots, r-1\}$. A cell vector is an element $u$ of the Euclidean space $\mathbb{R}^{\mathrm{Cell}_{k,r}}$ indexed by the [cells](../part-01/cell.md); write $u^{E}_{l,c}$ for its coordinate at the event cell $(l, c)$ and $u^{R}_{l}$ for its coordinate at the at-risk cell $l$.

The Kaplan–Meier factor of $u$ at grid index $i$ is

$$f_i(u) = 1 - \frac{\sum_{c=0}^{r-1} u^{E}_{i,c}}{u^{R}_{i}},$$

with real division, $x/0 = 0$.

For a horizon $m \in \{0, \dots, k-1\}$, the Aalen–Johansen map $A_m$ sends a cell vector $u$ to the real vector indexed by the [coordinates](../part-02/coord.md) $(\star, j)$ and $(c, j)$, $j \le m$, $c$ a cause, given by

$$A_m(u)_{(\star, j)} = \prod_{l \le j} f_l(u), \qquad A_m(u)_{(c, j)} = \sum_{l \le j} \Big(\prod_{i < l} f_i(u)\Big) \frac{u^{E}_{l,c}}{u^{R}_{l}},$$

with real division, $x/0 = 0$, empty products equal to $1$, and indices $i, l$ ranging over grid indices.

Write $DA_m(u)$ for the Fréchet derivative of $A_m$ at $u$ (taken to be the zero map if $A_m$ is not differentiable at $u$).

Let $m$ be a horizon and $u$ a cell vector with $u^{R}_{l} \ne 0$ for every grid index $l \le m$. Let $v$ be a cell vector, $a \in \mathrm{Coord}_{k,r}(m)$ a coordinate, $g : \mathbb{R} \to \mathbb{R}$ a function and $d$ a real number such that

- $A_m(u + t v)_a = g(t)$ for every real $t$, and
- $g$ has derivative $d$ at $t = 0$.

Then

$$\big(DA_m(u)\, v\big)_a = d.$$
