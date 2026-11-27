# Energy of the physical bar error

Let $P$ be a partition $0 = \xi_0 < \xi_1 < \dots < \xi_n = 1$ of $[0,1]$ and $I_P$ its nodal interpolant (the continuous piecewise linear function, constant outside $[0,1]$, that agrees with a given function at the nodes). If $L > 0$, then for all real $EA$, $q$ (real division, with $x/0 = 0$, so the identity also holds for $EA = 0$),

$$\int_0^L EA\, e'(x)^2\,dx = \frac{EA}{L}\,\alpha^2 \int_0^1 \hat e'(\xi)^2\,d\xi,$$

where $e(x) = u(x) - \alpha\,(I_P \hat u)(x/L)$, with $u(x) = \frac{q\, x (L - x)}{2\,EA}$, $\alpha = \frac{q L^2}{2\,EA}$ and $\hat u(\xi) = \xi(1-\xi)$, and $\hat e = \hat u - I_P \hat u$. Derivatives are pointwise, with value $0$ at the finitely many points where the derivative does not exist.
