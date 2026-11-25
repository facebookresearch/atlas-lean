# Chart Value

The value in the localization $k[x_0, \dots, x_n][x_i^{-1}]$ of a polynomial
$p = \sum_a c_a x^a$ in the coordinates other than $x_i$, at an integer character $t$: the sum
$\sum_a c_a x^a x_i^{e(a)}$, where $\mathrm{wt}(a) = \sum_{j \ne i} w_j a_j$ is the weighted degree
of $x^a$ and $e(a) = (t - \mathrm{wt}(a)) / w_i$ is integer division rounded down ($0$ when
$w_i = 0$). If $k$ has $w_i$ distinct $w_i$-th roots of unity and $p$ has character $t$ for their
action $x_j \mapsto \zeta^{w_j} x_j$, then $w_i$ divides $t - \mathrm{wt}(a)$ whenever $c_a \ne 0$,
so the division is exact.
