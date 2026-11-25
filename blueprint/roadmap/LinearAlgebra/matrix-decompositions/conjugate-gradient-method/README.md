# Conjugate gradient method

Let $n \ge 1$, let $A$ be a real symmetric positive definite $n \times n$ matrix with spectral condition number $\kappa = \lambda_{\max}/\lambda_{\min}$, let $b, x^\star \in \mathbb{R}^n$ with $Ax^\star = b$, and let $x_0 \in \mathbb{R}^n$. Then for every $k$ the $k$-th conjugate gradient iterate $x_k$ (Hestenes–Stiefel recurrence from $x_0$) satisfies

$$\|x_k - x^\star\|_A \le 2 \left(\frac{\sqrt{\kappa} - 1}{\sqrt{\kappa} + 1}\right)^k \|x_0 - x^\star\|_A,$$

where $\|v\|_A = \sqrt{v^{\mathsf T} A v}$ is the energy norm.

## Idea

The conjugate gradient method solves $Ax = b$ for positive definite $A$ using only products with $A$. Its $k$-th iterate minimizes the energy norm of the error over the affine Krylov space $x_0 + \operatorname{span}\{r_0, Ar_0, \dots, A^{k-1} r_0\}$. The error is therefore $p(A)(x_0 - x^\star)$ for the best polynomial $p$ of degree at most $k$ with $p(0) = 1$, and any particular polynomial gives an upper bound. Choosing a rescaled Chebyshev polynomial on the interval $[\lambda_{\min}, \lambda_{\max}]$ gives the factor above. This bound depends on $\sqrt{\kappa}$, whereas the corresponding bound for steepest descent depends on $\kappa$, which is why preconditioning, lowering $\kappa$, is so effective.

## Statements

- [The conjugate gradient error bound in terms of the condition number](energy-norm-iterate-sub-le-cond-num.md)
- [The conjugate gradient error bound](energy-norm-iterate-sub-le.md): a stronger form, for eigenvalues in an interval $[a, c]$
- [CG minimizes the energy norm of the error over the Krylov space](energy-norm-iterate-le.md): the iterate minimizes the energy-norm error over the Krylov space
- [The Chebyshev bound for Krylov energy minimizers](energy-norm-le-of-is-min-krylov.md): the Chebyshev bound for Krylov minimizers, used in the proof
- [CG stays in the Krylov space](iterate-x-sub-mem-krylov.md): the iterates stay in the Krylov space
- [State of the conjugate gradient method](state.md): the state $(x, r, d)$
- [One Hestenes–Stiefel conjugate gradient step](step.md): one Hestenes–Stiefel step
- [Initial conjugate gradient state](init.md): the initial state
- [Conjugate gradient state after $k$ steps](iterate.md): the state after $k$ steps
- [Krylov subspace](krylov.md): the Krylov subspace, also used by GMRES
- [Energy norm induced by a matrix](energy-norm.md): the energy norm
- [Spectral condition number of a positive definite matrix](cond-num.md): the spectral condition number

## Related topics

- [The Arnoldi relation](../arnoldi-and-lanczos-iterations/arnoldi-relation.md): the Lanczos recurrence, the Arnoldi process for symmetric operators, generates the Krylov spaces in which the conjugate gradient method works.
- [GMRES iterate](../gmres/is-gmresiterate.md): the Krylov method for general invertible systems, which minimizes the residual; its bound is also a polynomial approximation problem.
- [Minimax property of the Chebyshev polynomials](../../../Analysis/approximation-theory/minimax-property-of-the-chebyshev-polynomials/README.md)
- [Effective resistance and electrical networks](../../../GraphTheory/algebraic-graph-theory/part-01/effective-resistance-and-electrical-networks/README.md): Laplacian systems $Lv = b$ compute electrical potentials; fast Laplacian solvers precondition such iterative methods.
- [Nonlinear conjugate gradient methods](../../../Analysis/numerical-analysis/nonlinear-conjugate-gradient-methods/README.md):
  the extension to smooth unconstrained minimisation, which reduces to this method on strictly
  convex quadratics with exact line searches.
- [Condition number bound for linear systems](../perturbation-theory-for-linear-systems/condition-number-bound/norm-sub-div-norm-le.md): the condition number $\kappa(A) = \|A\|\,\|A^{-1}\|$, which for a positive definite $A$ in the 2-norm is the ratio $\kappa$ of extreme eigenvalues in the Chebyshev bound.
