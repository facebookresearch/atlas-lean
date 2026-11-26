# Aalen–Johansen influence coefficient in closed form

For a cell vector $u$ of event masses $u_{l,c}$ and at-risk masses $u_l$ on a finite grid, let $h_l = \sum_cu_{l,c}/u_l$, $S(l-) = \prod_{i<l}(1 - h_i)$ and $F_c(j) = \sum_{l\le j}S(l-)u_{l,c}/u_l$. If $l \le j$ and $1 - h_l \ne 0$, the influence coefficient of the cause-$c'$ increment at $l$ for $F_c(j)$ is $\mathbf 1\{c' = c\}S(l-)/u_l - (F_c(j) - F_c(l))/((1 - h_l)u_l)$. Real division uses $x/0 = 0$. (also when $u_l = 0$).
