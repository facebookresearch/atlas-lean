# Closed-form covariance of the influence vector of a sample subject

Let $k$ and $r$ be natural numbers. A subject is a point $w = ((T, J), C)$ of $\mathcal{W} = (\{0, \dots, k-1\} \times \{0, \dots, r-1\}) \times \{0, \dots, k-1\}$: an event-time grid index $T$, a cause $J$ and a censoring grid index $C$.

Let $\mu$ be a measure on $\mathcal{W}$, let $(\Omega, P)$ be a probability space, and let $W_0 : \Omega \to \mathcal{W}$ have law $\mu$ under $P$: $W_0$ is $P$-almost everywhere measurable and the image of $P$ under $W_0$ is $\mu$. Let $m \in \{0, \dots, k-1\}$ be a horizon with $y_\mu(m) \ne 0$, where, for a grid index $l$ and a cause $c$,

$$e_\mu(l, c) = \mu\{(T, J, C) : \min(T, C) = l,\ T \le C,\ J = c\}, \qquad y_\mu(l) = \mu\{(T, J, C) : l \le \min(T, C)\}.$$

**Cell vectors.** A cell vector is an element $u$ of $\mathbb{R}^{\mathrm{Cell}_{k,r}}$ (see [cells](../part-01/cell.md)), with coordinates $u^{E}_{l,c}$ at the event cells and $u^{R}_{l}$ at the at-risk cells. The mean cell vector $\bar u$ has $\bar u^{E}_{l,c} = e_\mu(l, c)$ and $\bar u^{R}_{l} = y_\mu(l)$. The cell vector of a subject $w = ((T, J), C)$ has coordinates

$$v(w)^{E}_{l,c} = \mathbf{1}[\min(T, C) = l,\ T \le C,\ J = c], \qquad v(w)^{R}_{l} = \mathbf{1}[l \le \min(T, C)].$$

**The map and the influence vector.** With the Kaplan–Meier factors $f_i(u) = 1 - \big(\sum_{c} u^{E}_{i,c}\big) / u^{R}_{i}$, the [Aalen–Johansen map](../part-01/aj-map.md) $A_m$ sends $u$ to the vector indexed by the [coordinates](coord.md) $a \in \mathrm{Coord}_{k,r}(m)$ given by

$$A_m(u)_{(\star, j)} = \prod_{l \le j} f_l(u), \qquad A_m(u)_{(c, j)} = \sum_{l \le j} \Big(\prod_{i < l} f_i(u)\Big) \frac{u^{E}_{l,c}}{u^{R}_{l}}.$$

The [influence vector](../part-04/influence.md) of a subject $w$ is $\mathrm{IF}(w) = DA_m(\bar u)\big(v(w)\big)$, where $DA_m(\bar u)$ is the Fréchet derivative of $A_m$ at $\bar u$ (taken to be the zero map if $A_m$ is not differentiable there).

**Coefficients.** For grid indices $j, l$ and causes $c, c'$, the [Kaplan–Meier](../part-05/km-coeff.md) and [Aalen–Johansen](../part-01/aj-coeff.md) influence coefficients at a cell vector $u$ are

$$\kappa_j(u; l) = [\,l \le j\,] \cdot \frac{-\prod_{i \le j,\, i \ne l} f_i(u)}{u^{R}_{l}},$$

$$a_{j,c}(u; l, c') = \frac{[\,l \le j \text{ and } c' = c\,] \prod_{i < l} f_i(u)}{u^{R}_{l}} - \frac{\sum_{l < l' \le j} \big(\prod_{i < l',\, i \ne l} f_i(u)\big)\, u^{E}_{l',c} / u^{R}_{l'}}{u^{R}_{l}},$$

where $[\cdot]$ is $1$ when the condition holds and $0$ otherwise. The [influence coefficients](../part-04/influence-coeff.md) of a coordinate are $\gamma_{(\star, j)}(l, c') = \kappa_j(\bar u; l)$ for every cause $c'$, and $\gamma_{(c, j)}(l, c') = a_{j,c}(\bar u; l, c')$.

**Gram form.** For arrays $\gamma, \gamma'$ indexed by grid indices and causes, the [increment Gram form](../part-04/increment-cov.md) at $u$ is

$$G(u; \gamma, \gamma') = \sum_{l} \left( \sum_{c} \gamma(l, c)\, \gamma'(l, c)\, u^{E}_{l,c} - \frac{\big(\sum_{c} \gamma(l, c)\, u^{E}_{l,c}\big) \big(\sum_{c} \gamma'(l, c)\, u^{E}_{l,c}\big)}{u^{R}_{l}} \right).$$

All quotients above use real division with $x/0 = 0$, empty products are $1$, and indices $i, l, l'$ range over grid indices.

**Statement.** For all coordinates $a, b \in \mathrm{Coord}_{k,r}(m)$,

$$\mathrm{Cov}_P\big(\mathrm{IF}(W_0)_a,\ \mathrm{IF}(W_0)_b\big) = G(\bar u; \gamma_a, \gamma_b),$$

where $\mathrm{Cov}_P(X, Y) = \int (X - \textstyle\int X \, dP)(Y - \textstyle\int Y \, dP) \, dP$.
