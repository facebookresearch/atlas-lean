# Forward Finsler distance

Let $F$ be a Finsler metric on a manifold $M$. The forward
Finsler distance from $x \in M$ to $y \in M$ is the value in $[0, \infty]$

$$
d_F(x, y) = \inf_\gamma \int_0^1 F(\gamma(t), \gamma'(t))\, dt,
$$

the infimum over all $C^1$ paths $\gamma : [0, 1] \to M$ from $x$ to $y$; it is $\infty$ when
there is no such path.

It is not symmetric unless $F$ is reversible.

## Sources

- Bao–Chern–Shen, *An Introduction to Riemann–Finsler Geometry*, §6.2. The formula is that of Mathlib's `riemannianEDist` with `‖v‖ₑ` replaced by `F v`.
