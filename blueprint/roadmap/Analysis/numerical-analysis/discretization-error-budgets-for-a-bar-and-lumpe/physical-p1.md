# Physical P1 reconstruction of the bar displacement

Let $P$ be a partition $0 = \xi_0 < \xi_1 < \dots < \xi_n = 1$ of $[0,1]$ and $I_P$ its nodal interpolant (the continuous piecewise linear function, constant outside $[0,1]$, that agrees with a given function at the nodes). For real $EA$, $L$, $q$, the physical P1 reconstruction is

$$u_h(x) = \alpha\,(I_P \hat u)(x/L), \qquad \alpha = \frac{q L^2}{2\,EA}, \qquad \hat u(\xi) = \xi(1-\xi).$$

Real division by zero is $0$: $\alpha = 0$ when $EA = 0$, and $x / L = 0$ when $L = 0$, so then $u_h$ is the constant $\alpha\,(I_P \hat u)(0) = 0$.
