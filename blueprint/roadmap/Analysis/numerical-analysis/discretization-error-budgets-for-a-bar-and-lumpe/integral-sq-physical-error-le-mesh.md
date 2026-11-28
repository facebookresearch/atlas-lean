# Mesh bound on the squared L² norm of the physical bar error

Let $P$ be a partition $0 = \xi_0 < \xi_1 < \dots < \xi_n = 1$ of $[0,1]$ and $I_P$ its nodal interpolant (the continuous piecewise linear function, constant outside $[0,1]$, that agrees with a given function at the nodes). Let $h$ be the mesh size of $P$ (its largest cell length). If $L > 0$, then for all real $EA$, $q$ (real division, with $x/0 = 0$, so the bound also holds for $EA = 0$),

$$\int_0^L e(x)^2\,dx \le L\,\alpha^2 \cdot 4\left(\frac{h}{\pi}\right)^{4},$$

where $e(x) = u(x) - \alpha\,(I_P \hat u)(x/L)$, with $u(x) = \frac{q\, x (L - x)}{2\,EA}$, $\alpha = \frac{q L^2}{2\,EA}$ and $\hat u(\xi) = \xi(1-\xi)$.
