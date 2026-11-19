# Variational inequality of the minimizing-movement step

Let $H$ be a real inner product space, $F : H \to \mathbb{R}$ $\lambda$-convex, i.e.

$$F((1-t)a + tb) \le (1-t) F(a) + t F(b) - t(1-t) \tfrac{\lambda}{2} \|a - b\|^2 \qquad (t \in [0, 1]),$$

and $h > 0$. If $y$ is a [minimizing-movement step](is-minimizing-movement-step.md) from $x$, then
for every $z \in H$,

$$\langle x - y, z - y \rangle \le h \bigl(F(z) - F(y)\bigr) - h \tfrac{\lambda}{2} \|z - y\|^2 .$$

Thus $(x - y)/h$ is a $\lambda$-subgradient of $F$ at $y$; for differentiable $F$ this is the
implicit Euler equation $y = x - h \nabla F(y)$. Proof: compare $y$ with $(1-t)y + tz$, use
$\lambda$-convexity, divide by $t$ and let $t \downarrow 0$. $\lambda$ may be any real number.
