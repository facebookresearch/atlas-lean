# The GMRES polynomial bound

If $x$ is a $k$-th GMRES iterate, then
$\|b - Ax\|_2 \le \|p(A)\, r_0\|_2$ for every real polynomial $p$ of degree at most $k$ with
$p(0) = 1$. Since the GMRES residual is itself of the form $p(A) r_0$,
GMRES solves the polynomial approximation problem "minimize $\|p(A) r_0\|$ over $p \in P_k$,
$p(0) = 1$": its convergence is governed by how small a polynomial normalized at the origin can be
on the spectrum (or pseudospectra) of $A$.

## Background

- [Minimax property of the Chebyshev polynomials](../../../Analysis/approximation-theory/minimax-property-of-the-chebyshev-polynomials/README.md): the extremal polynomial problem on an interval that gives the classical Chebyshev bounds for CG and for GMRES on symmetric definite matrices.
- [The Chebyshev bound for Krylov energy minimizers](../conjugate-gradient-method/energy-norm-le-of-is-min-krylov.md): the analogous energy-norm statement for CG.

## Sources

- L. N. Trefethen and D. Bau III, Numerical Linear Algebra, SIAM (1997), Lecture 35 (the GMRES polynomial approximation problem).
- T. A. Driscoll, K.-C. Toh and L. N. Trefethen, From potential theory to matrix iterations in six steps, SIAM Rev. 40 (1998), 547–578.
