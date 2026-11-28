# Grouped censored data of the first n observations on a grid

Let $t_0 < t_1 < \dots < t_{k-1}$ be a strictly increasing grid, $y_0, y_1, \dots$ a sequence of observations $y_i = (T_i, \delta_i) \in \mathbb R \times \mathbb R$, and $n \in \mathbb N$. The grouped censored data of the first $n$ observations at the grid has observation times $t_0, \dots, t_{k-1}$ and, at each grid time $t_j$,

$$d_j = \#\{i < n : y_i = (t_j, 1)\}, \qquad c_j = \#\{i < n : T_i = t_j \text{ and } y_i \ne (t_j, 1)\}$$

deaths and censorings respectively. An observation with $\delta_i = 1$ counts as a death and any other value of $\delta_i$ as a censoring; observations whose time is not a grid point are not counted.
