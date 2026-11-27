# Projection methods for linear systems

A projection method for $Ax = b$ seeks an approximation in an affine search space $x_0 + \mathcal{K}$ whose residual is orthogonal to a constraint space $\mathcal{L}$. Taking $\mathcal{L} = \mathcal{K}$ for a symmetric positive definite matrix minimizes the energy norm of the error, and taking $\mathcal{L} = A\mathcal{K}$ minimizes the residual; with one-dimensional spaces these give the steepest descent and minimal residual iterations, whose convergence rates come from the Kantorovich inequality and from the field of values. Krylov subspace methods such as conjugate gradients and GMRES are the many-dimensional cases.

- [Projection method](projection-method.md)
- [The projected system is nonsingular in the two standard cases](projected-system-is-nonsingular.md)
- [Galerkin projection minimizes the energy norm of the error](galerkin-projection-minimizes-the-energy-norm-of-the-error.md)
- [Minimal residual projection minimizes the residual](minimal-residual-projection-minimizes-the-residual.md)
- [Steepest descent iteration](steepest-descent-iteration.md)
- [Convergence of steepest descent](steepest-descent-converges.md)
- [Convergence of the minimal residual iteration](minimal-residual-iteration-converges.md)

## Related topics

- [Conjugate gradient method](../../../../LinearAlgebra/matrix-decompositions/conjugate-gradient-method/README.md)
- [Kantorovich inequality](../../../inequalities/kantorovich-bhatia-davis-and-popoviciu-inequalit/kantorovich-inequality.md)
