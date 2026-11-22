# Quadratic identity for the Tikhonov functional at a normal-equation solution

Let $H$ and $K$ be Hilbert spaces over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, $A : H \to K$ a
bounded linear operator, $b \in K$ and $\Lambda \in \mathbb{R}$. If $x_0$ solves the normal equations
$(A^* A + \Lambda I) x_0 = A^* b$, then for every $x \in H$ the [Tikhonov
functional](tikhonov-functional.md) satisfies

$$J(x) = J(x_0) + \|A(x - x_0)\|^2 + \Lambda \|x - x_0\|^2:$$

the cross term vanishes by the normal equations.
