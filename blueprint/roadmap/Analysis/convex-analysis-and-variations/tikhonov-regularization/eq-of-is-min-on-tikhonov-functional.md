# Tikhonov minimizers solve the normal equations

Let $H$ and $K$ be Hilbert spaces over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, $A : H \to K$ a
bounded linear operator, $b \in K$ and $\Lambda > 0$. If $x_0$ solves the normal equations
$(A^* A + \Lambda I) x_0 = A^* b$ and $x$ minimizes the [Tikhonov functional](tikhonov-functional.md)
$J(x) = \|Ax - b\|^2 + \Lambda \|x\|^2$ over $H$, then $x = x_0$.
