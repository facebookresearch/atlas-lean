# GMRES

The generalized minimal residual method minimizes $\|b - Ax\|_2$ over the affine Krylov space $x_0 + \mathcal{K}_k(A, r_0)$. Its residual is $p(A)r_0$ for the polynomial $p$ of degree at most $k$ with $p(0) = 1$ that minimizes $\|p(A)r_0\|_2$, so GMRES convergence is a problem of polynomial approximation (Trefethen and Bau, Lecture 35). Bounds in terms of the spectrum alone need a caveat: for a diagonalizable $A = V \Lambda V^{-1}$ the relative residual is at most $\kappa(V) \min_p \max_\lambda |p(\lambda)|$, the maximum over the eigenvalues $\lambda$ of $A$, with $\kappa(V) = 1$ when $A$ is normal; for a nonnormal $A$ the eigenvalues alone can be misleading. For an invertible $n \times n$ matrix it terminates in at most $n$ steps.

- [GMRES iterate](is-gmresiterate.md)
- [Krylov matrix](krylov-matrix.md)
- [The Krylov space is the column space of the Krylov matrix](mem-krylov-iff.md)
- [Existence of GMRES iterates](exists-is-gmresiterate.md)
- [The GMRES polynomial bound](rss-le-of-is-gmresiterate.md)
- [Finite termination of GMRES](mul-vec-eq-of-is-gmresiterate-dim.md)

## Related topics

- [Arnoldi and Lanczos iterations](../arnoldi-and-lanczos-iterations/README.md)
- [Conjugate gradient method](../conjugate-gradient-method/README.md)
- [Linear least squares](../linear-least-squares/README.md)
- [Minimax property of the Chebyshev polynomials](../../../Analysis/approximation-theory/minimax-property-of-the-chebyshev-polynomials/README.md)
