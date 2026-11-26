# Cumulative incidence accrued after a time

For a cell vector $u$ of event masses $u_{l,c}$ and at-risk masses $u_l$ on a finite grid, let $h_l = \sum_cu_{l,c}/u_l$, $S(l-) = \prod_{i<l}(1 - h_i)$ and $F_c(j) = \sum_{l\le j}S(l-)u_{l,c}/u_l$. For $l \le j$, $F_c(j) - F_c(l) = \sum_{l<l'\le j}S(l'-)u_{l',c}/u_{l'}$. Real division uses $x/0 = 0$.
