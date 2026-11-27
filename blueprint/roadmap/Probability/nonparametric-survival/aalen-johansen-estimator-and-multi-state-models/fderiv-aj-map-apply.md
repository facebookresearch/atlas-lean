# Derivative of the Aalen–Johansen map in increment coordinates

For a cell vector $u$ of event masses $u_{l,c}$ and at-risk masses $u_l$ on a finite grid, let $h_l = \sum_cu_{l,c}/u_l$, $S(l-) = \prod_{i<l}(1 - h_i)$ and $F_c(j) = \sum_{l\le j}S(l-)u_{l,c}/u_l$. If $u_l \ne 0$ for $l \le m$, every coordinate of the derivative of the joint Kaplan–Meier and Aalen–Johansen map at $u$ in direction $v$ is $\sum_{l,c'}\gamma_{l,c'}(v_{l,c'} - (u_{l,c'}/u_l)v_l)$ with the influence coefficients $\gamma$.
