# Finsler metric

Let $M$ be a $C^\infty$ manifold (possibly with boundary or corners)
modelled on a finite-dimensional real normed space $E$, so that each tangent space $T_xM$ is $E$.
A $C^\infty$ Finsler metric on $M$ is a continuous function $F : TM \to \mathbb{R}$ that is
$C^\infty$ off the zero section, satisfies $F(x, v) > 0$ for every $x \in M$ and every nonzero
$v \in T_xM$, is positively homogeneous of degree one on each fiber, that is
$F(x, cv) = c\,F(x, v)$ for all $x \in M$, $v \in T_xM$ and real $c > 0$, and is strongly convex:
for every $x \in M$ and all nonzero $v, w \in E$, the second derivative at $v$ of the function
$u \mapsto F(x, u)^2$ on $E$ satisfies $D^2\big(F(x, \cdot)^2\big)(v)(w, w) > 0$.

## Sources

- Bao–Chern–Shen, *An Introduction to Riemann–Finsler Geometry*, §1.1, where $F$ takes values in $[0, \infty)$ and the Hessian is that of $F^2/2$.
