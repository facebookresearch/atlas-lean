# GMRES

For a real $n \times n$ matrix $A$, a right-hand side $b$, an initial guess $x_0$ with residual $r_0 = b - Ax_0$ and a step $k$, a vector $x$ is a $k$-th GMRES iterate if $x - x_0$ lies in the Krylov subspace $\mathcal{K}_k(A, r_0) = \operatorname{span}\{r_0, Ar_0, \dots, A^{k-1} r_0\}$ and $x$ minimizes $\|b - Ay\|_2$ over all $y \in x_0 + \mathcal{K}_k(A, r_0)$.

## Idea

The generalized minimal residual method solves $Ax = b$ for a general square matrix by minimizing the residual over growing Krylov spaces. Writing $y = x_0 + K_k c$ with the Krylov matrix $K_k$ turns each step into a small least-squares problem, so iterates always exist. The residual of an iterate is $p(A) r_0$ for a polynomial $p$ of degree at most $k$ with $p(0) = 1$, and it is at least as small as $\|p(A) r_0\|_2$ for every such polynomial. For a normal matrix this bound reduces to how small such a polynomial can be on the spectrum; for a diagonalizable matrix $A = V \Lambda V^{-1}$ the spectral bound holds up to the factor $\|V\|_2 \|V^{-1}\|_2$; for a nonnormal matrix the spectrum alone can mislead: $p(z) = 1 - z$ vanishes on the spectrum of the Jordan block $\begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}$, but $p(A) \ne 0$. For an invertible matrix, the $n$-th iterate solves the system exactly in exact arithmetic. In practice the Arnoldi iteration supplies an orthonormal basis of the Krylov space.

## Statements

- [GMRES iterate](is-gmresiterate.md)
- [Existence of GMRES iterates](exists-is-gmresiterate.md): iterates exist
- [The GMRES polynomial bound](rss-le-of-is-gmresiterate.md): the polynomial bound on the residual
- [Finite termination of GMRES](mul-vec-eq-of-is-gmresiterate-dim.md): finite termination
- [Krylov matrix](krylov-matrix.md): the Krylov matrix
- [The Krylov space is the column space of the Krylov matrix](mem-krylov-iff.md): the Krylov space is the column space of the Krylov matrix

## Background

- [Linear least squares](../linear-least-squares/README.md): each GMRES iterate solves a least-squares problem over the Krylov space.

## Related topics

- [The Arnoldi relation](../arnoldi-and-lanczos-iterations/arnoldi-relation.md): practical GMRES builds an orthonormal basis of the Krylov space with the Arnoldi process.
- [The conjugate gradient error bound in terms of the condition number](../conjugate-gradient-method/energy-norm-iterate-sub-le-cond-num.md): the Krylov method for symmetric positive definite systems, which minimizes the energy norm of the error instead of the residual.
- [Minimax property of the Chebyshev polynomials](../../../Analysis/approximation-theory/minimax-property-of-the-chebyshev-polynomials/README.md)
