# Hurwitz criterion for $2 \times 2$ real matrices

A real $2 \times 2$ matrix $A$ is Hurwitz, that is, both of its complex eigenvalues have negative real part, if and only if
$\operatorname{tr} A < 0$ and $\det A > 0$.

The eigenvalues are the roots of $\lambda^2 - (\operatorname{tr} A)\lambda + \det A$. If they are real, both are negative
exactly when their sum is negative and their product positive; if they are a complex-conjugate pair, their common real
part is $\operatorname{tr} A/2$ and their product $\lvert\lambda\rvert^2$ is positive.

## Depends on

- [Hurwitz matrix](nonsingular-m-matrices/is-hurwitz.md), for the definition

## Proof depends on

## Expansion

Check the statement against a textbook locator for the trace-determinant classification of planar linear systems, and
keep it as the shared criterion for stability arguments that need it; results whose Jacobian is triangular can read the
eigenvalues off the diagonal instead.

## Sources

- M. W. Hirsch, S. Smale and R. L. Devaney, *Differential Equations, Dynamical Systems, and an Introduction to Chaos*, 3rd edition, Academic Press, 2013, the trace-determinant plane.
