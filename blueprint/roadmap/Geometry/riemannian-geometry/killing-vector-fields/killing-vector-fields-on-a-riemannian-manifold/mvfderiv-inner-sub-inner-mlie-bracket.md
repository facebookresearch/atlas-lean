# The Lie derivative of the metric via the Levi-Civita connection

Let $M$ be a smooth
manifold modeled on a finite-dimensional real normed space (possibly with corners), with a smooth
Riemannian metric $g = \langle \cdot, \cdot \rangle$ and Levi-Civita connection $\nabla$, and let
$X$, $Y$, $Z$ be vector fields on $M$ that are differentiable at a point $x$. Write $[\cdot, \cdot]$
for the Lie bracket of vector fields and $X_x \langle Y, Z \rangle$ for the derivative at $x$ of
the function $y \mapsto \langle Y_y, Z_y \rangle$ in the direction $X_x$. Then

$$
X_x \langle Y, Z \rangle - \langle [X, Y]_x, Z_x \rangle - \langle Y_x, [X, Z]_x \rangle
= \langle \nabla_{Y_x} X, Z_x \rangle + \langle Y_x, \nabla_{Z_x} X \rangle.
$$

The left-hand side is $(\mathcal{L}_X g)(Y, Z)$ at $x$.
