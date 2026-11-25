# Zero load of the fixed-fixed bar

Let $P$ be a partition of $[0,1]$, $I_P$ the continuous piecewise-linear nodal interpolant on $P$, and $\hat u(\xi) = \xi(1-\xi)$. For any $EA, L \in \mathbb{R}$ and load $q = 0$, with $\alpha = \dfrac{q L^2}{2\,EA}$, $u(x) = \dfrac{q\,x\,(L-x)}{2\,EA}$, $u_h(x) = \alpha\,(I_P\hat u)(x/L)$ and $e = u - u_h$:

$$\alpha = 0, \qquad u(x) = 0, \qquad u_h(x) = 0, \qquad e(x) = 0 \quad \text{for all } x \in \mathbb{R}.$$

No condition on $EA$ or $L$ is imposed: divisions follow the convention $x/0 = 0$, so for $EA = 0$ the quotients $\alpha$ and $u(x)$ are $0/0 = 0$, and for $L = 0$ the argument $x/L$ is $0$.
