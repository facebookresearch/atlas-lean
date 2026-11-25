# Solutions of the normal equations minimize the Tikhonov functional

Let $H$ and $K$ be Hilbert spaces over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, $A : H \to K$ a
bounded linear operator, $b \in K$ and $\Lambda \ge 0$. If $x_0$ solves the normal equations
$(A^* A + \Lambda I) x_0 = A^* b$, then $x_0$ minimizes the [Tikhonov
functional](tikhonov-functional.md) $J(x) = \|Ax - b\|^2 + \Lambda \|x\|^2$ over $H$.
