# Smoothness of the Levi-Civita connection

Let $M$ be a smooth manifold, possibly with
boundary or corners, modelled on a finite-dimensional real normed space, whose tangent bundle
carries a smooth Riemannian metric. Then Mathlib's Levi-Civita connection
`CovariantDerivative.leviCivitaConnection` of $M$ is a smooth covariant derivative: for every
smooth vector field $Y$ on $M$, the section $x \mapsto \nabla Y(x)$ of the bundle of
endomorphisms of the tangent bundle is smooth.

## Sources

- the Koszul formula (O. Knill, Some Fundamental Theorems in Mathematics, arXiv:1807.08416, §38), read in the local frame of a chart, where it expresses the coefficients of the connection through the metric coefficients, their first derivatives and the inverse of the Gram matrix of the metric.
