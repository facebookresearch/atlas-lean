# Conjugate gradient method

- [Energy norm induced by a matrix](energy-norm.md)
- [Krylov subspace](krylov.md)
- [State of the conjugate gradient method](state.md)
- [One Hestenes–Stiefel conjugate gradient step](step.md)
- [Initial conjugate gradient state](init.md)
- [Conjugate gradient state after $k$ steps](iterate.md)

## Krylov spaces

- [CG stays in the Krylov space](iterate-x-sub-mem-krylov.md)
- [CG minimizes the energy norm of the error over the Krylov space](energy-norm-iterate-le.md)

## The Chebyshev bound

- [The Chebyshev bound for Krylov energy minimizers](energy-norm-le-of-is-min-krylov.md)
- [The conjugate gradient error bound](energy-norm-iterate-sub-le.md)
- [Spectral condition number of a positive definite matrix](cond-num.md)
- [The conjugate gradient error bound in terms of the condition number](energy-norm-iterate-sub-le-cond-num.md)

## Related topics

- [Arnoldi and Lanczos iterations](../arnoldi-and-lanczos-iterations/README.md)
- [GMRES](../gmres/README.md)
- [Minimax property of the Chebyshev polynomials](../../../Analysis/approximation-theory/minimax-property-of-the-chebyshev-polynomials/README.md)
- [Effective resistance and electrical networks](../../../GraphTheory/algebraic-graph-theory/part-01/effective-resistance-and-electrical-networks/README.md): Laplacian systems $Lv = b$ compute electrical potentials; fast Laplacian solvers precondition such iterative methods.
- [Nonlinear conjugate gradient methods](../../../Analysis/numerical-analysis/nonlinear-conjugate-gradient-methods/README.md):
  the extension to smooth unconstrained minimisation, which reduces to this method on strictly
  convex quadratics with exact line searches.
- [Perturbation theory for linear systems](../perturbation-theory-for-linear-systems/README.md): the condition number $\kappa(A) = \|A\|\,\|A^{-1}\|$, which for a positive definite $A$ in the 2-norm is the ratio $\kappa$ of extreme eigenvalues in the Chebyshev bound.
