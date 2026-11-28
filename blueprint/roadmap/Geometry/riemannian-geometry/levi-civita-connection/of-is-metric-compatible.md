# Mathlib's metric compatibility implies `IsMetricCompatible`

Let $\nabla$ be a covariant
derivative on the tangent bundle of a smooth manifold $M$ (possibly with corners) modelled on a
finite-dimensional real normed space, with a smooth Riemannian metric on its tangent bundle.
Suppose $\nabla$ is compatible with the metric in the sense of Mathlib's
`CovariantDerivative.IsMetricCompatible`: at every point $x \in M$,
$X \langle Y, Z \rangle = \langle \nabla_X Y, Z \rangle + \langle Y, \nabla_X Z \rangle$ for all
vector fields $X, Y, Z$ differentiable at $x$. Then $\nabla$ satisfies `IsMetricCompatible`, the
same product rule for all smooth vector fields $Y, Z$ and every tangent vector.

## Sources

- direct from the two definitions, original to this formalization: Mathlib's product rule is applied to a vector field that extends the given tangent vector.
