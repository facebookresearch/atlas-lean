# P1 bar reconstruction is the scaled Galerkin solution

Let $P$ be a partition $0 = \xi_0 < \xi_1 < \dots < \xi_n = 1$ of $[0,1]$ and $I_P$ its nodal interpolant (the continuous piecewise linear function, constant outside $[0,1]$, that agrees with a given function at the nodes). Let $c = (c_0, \dots, c_n)$ solve the P1 Galerkin system of the unit problem $-\hat u'' = 2$: $c_0 = c_n = 0$ and $(Kc)_j = F_j$ at every interior node $j$, with the assembled stiffness matrix $K$ and the load vector $F_j = \int_0^1 2\,\varphi_j$ for the hat functions $\varphi_j$. Then for all real $EA$, $L$, $q$, $x$ (real division, with $x/0 = 0$, so the identity also holds for $EA = 0$),

$$\alpha\,(I_P \hat u)(x/L) = \alpha\, p_c(x/L),$$

where $p_c$ is the continuous function with nodal values $c$ that is affine on each cell $[\xi_{i}, \xi_{i+1}]$ and constant on each exterior ray, equal to $c_0$ on $(-\infty, 0]$ and to $c_n$ on $[1, \infty)$ (as $I_P \hat u$ is), $\alpha = \frac{q L^2}{2\,EA}$ and $\hat u(\xi) = \xi(1-\xi)$.
