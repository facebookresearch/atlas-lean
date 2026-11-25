# Coefficient error bounded by the residual

Consider a bar on $[0, L]$ with axial stiffness $EA$, discretized by the two-cell mesh with nodes $0, L/2, L$. Let $\varphi$ be the hat function of the interior node of the mesh $0 < \tfrac12 < 1$ of $[0, 1]$ (piecewise linear, $\varphi(0) = \varphi(1) = 0$, $\varphi(\tfrac12) = 1$). For a uniform load $q$ let $u_h(x) = \alpha\,(I\hat u)(x/L)$ with $\alpha = qL^2/(2EA)$, $\hat u(\xi) = \xi(1 - \xi)$ and $I$ the piecewise-linear nodal interpolant on that mesh, and let $c^\ast = u_h(L/2)$. For an approximate interior coefficient $c$, the residual is $r = qL/2 - (4EA/L)\,c$. If $EA > 0$ and $L > 0$, then for all $q, c \in \mathbb{R}$

$$|c^\ast - c| \le \frac{L\,|r|}{4\,EA}.$$
