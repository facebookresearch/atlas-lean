# Energy norm of the midpoint quadrature error

Consider a bar on $[0, L]$ with axial stiffness $EA$, discretized by the two-cell mesh with nodes $0, L/2, L$. Let $\varphi$ be the hat function of the interior node of the mesh $0 < \tfrac12 < 1$ of $[0, 1]$ (piecewise linear, $\varphi(0) = \varphi(1) = 0$, $\varphi(\tfrac12) = 1$). For the quadratic load $q(x) = Q\,(x/L)^2$ let $\beta = QL^2/EA$ and $K = 4EA/L$. The exact-load coefficient is $c_{\mathrm{ex}} = F/K$ with $F = \int_0^L Q\,(x/L)^2\,\varphi(x/L)\,dx$, and the midpoint coefficient is $c_{\mathrm{mid}} = F_{\mathrm{mid}}/K$ with $F_{\mathrm{mid}} = \tfrac{L}{2}\big(q(L/4)\,\varphi(1/4) + q(3L/4)\,\varphi(3/4)\big)$. If $EA > 0$ and $L > 0$, then for every $Q \in \mathbb{R}$

$$\int_0^L EA\,\Big(\frac{d}{dx}\big(c_{\mathrm{ex}}\,\varphi(x/L) - c_{\mathrm{mid}}\,\varphi(x/L)\big)\Big)^2\,dx = \frac{4\,EA}{L}\Big(\frac{\beta}{384}\Big)^2.$$
