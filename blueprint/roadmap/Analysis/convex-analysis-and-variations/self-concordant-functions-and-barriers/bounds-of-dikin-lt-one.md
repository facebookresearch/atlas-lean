# Bounds on a self-concordant function in the Dikin ellipsoid

Let $E$ be a finite-dimensional real normed space, $F$ [self-concordant](is-self-concordant.md) on $Q \subseteq E$, $x \in Q$ and $h \in E$ with $r = |h|_x < 1$. With $\rho(s) = -\log(1 - s) - s$,

$$
F(x) + DF(x)[h] + \rho(-r) \le F(x + h) \le F(x) + DF(x)[h] + \rho(r) .
$$

Here $D^kF(x)[h, \ldots, h]$ denotes the $k$-th derivative at $t = 0$ of the restriction $t \mapsto F(x + t h)$ of $F$ to the line through $x$ in direction $h$, and $|h|_x = (D^2F(x)[h, h])^{1/2}$ is the local norm defined by $F$ at $x$. These bounds replace the quadratic model of a function with Lipschitz Hessian, and give the affine-invariant analysis of the damped Newton method. The source also notes that the lower bound holds for every $h$ with $x + h \in Q$, not only for $|h|_x < 1$; the statement above is restricted to $|h|_x < 1$.

## Sources

- A. Nemirovski, *Interior Point Polynomial Time Methods in Convex Programming*, lecture notes (Georgia Tech, 2004); author PDF at <https://www2.isye.gatech.edu/~nemirovs/Lect_IPM.pdf>, Section 2.2, item I, (2.4)–(2.5).
