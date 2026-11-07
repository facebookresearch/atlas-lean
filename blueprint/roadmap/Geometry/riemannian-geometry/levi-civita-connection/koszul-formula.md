# Koszul formula

Let $M$ be a smooth manifold, modelled with corners on a finite-dimensional
real normed space, whose tangent bundle carries a smooth Riemannian metric $\langle \cdot, \cdot
\rangle$, and let $\nabla$ be a smooth covariant derivative on the tangent bundle of $M$ that is
torsion-free and compatible with the metric. Then for all smooth vector fields $X$, $Y$, $Z$ on
$M$ and every point $x \in M$, evaluating every term at $x$,

$$2 \langle \nabla_X Y, Z \rangle = X \langle Y, Z \rangle + Y \langle X, Z \rangle -
Z \langle X, Y \rangle - \langle X, [Y, Z] \rangle - \langle Y, [X, Z] \rangle +
\langle Z, [X, Y] \rangle,$$

where $\nabla_X Y$ at $x$ is the covariant derivative of $Y$ in the direction $X(x)$,
$X \langle Y, Z \rangle$ at $x$ is the derivative of the function $y \mapsto \langle Y(y), Z(y)
\rangle$ in the direction $X(x)$, and $[\cdot, \cdot]$ is the Lie bracket of vector fields.

## Sources

- J.-L. Koszul (course notes, 1950s); cf. do Carmo, Riemannian Geometry. Listed as §38 additional statement in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `koszul_formula`.
