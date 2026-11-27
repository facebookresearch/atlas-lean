# Stationary iterative methods

A splitting $A = M - N$ turns $Ax = b$ into the fixed-point iteration $x_{k+1} = M^{-1}N x_k + M^{-1}b$, which converges for every right-hand side and every starting vector exactly when the spectral radius of $M^{-1}N$ is less than $1$. For a matrix $A = D - E - F$ with nonzero diagonal $D$ and strictly lower and upper parts $-E$ and $-F$, the Jacobi, Gauss–Seidel and SOR iterations take $M = D$, $M = D - E$ and $M = D/\omega - E$; diagonal dominance, irreducibility, positive definiteness and consistent ordering give their convergence and, for SOR, the optimal relaxation parameter.

## Splittings and convergence

- [Splitting iteration](splitting-iteration.md)
- [Powers of a matrix tend to zero exactly when its spectral radius is less than one](matrix-powers-tend-to-zero.md)
- [Convergence of stationary iterations](convergence-of-stationary-iterations.md)

## Jacobi and Gauss–Seidel

- [Jacobi and Gauss–Seidel iterations](jacobi-and-gauss-seidel-iteration-matrices.md)
- [Gauss–Seidel converges for strictly diagonally dominant matrices](gauss-seidel-converges-for-strictly-diagonally-dominant-matrices.md)
- [Irreducible matrix](irreducible-matrix.md)
- [Eigenvalues on the boundary of the Gershgorin region](taussky-boundary-theorem.md)
- [Irreducibly diagonally dominant matrices are nonsingular](irreducibly-diagonally-dominant-matrices-are-nonsingular.md)
- [Jacobi and Gauss–Seidel converge for irreducibly diagonally dominant matrices](jacobi-and-gauss-seidel-converge-for-irreducibly-diagonally-dominant-matrices.md)

## Successive overrelaxation

- [Successive overrelaxation](sor-iteration.md)
- [Ostrowski–Reich theorem](ostrowski-reich-theorem.md)
- [Consistently ordered matrix](consistently-ordered-matrix.md)
- [Young's relation between SOR and Jacobi eigenvalues](young-sor-jacobi-eigenvalue-relation.md)
- [For two-cyclic matrices the Gauss–Seidel spectral radius is the square of the Jacobi one](gauss-seidel-spectral-radius-is-the-square-of-jacobi.md)
- [Optimal SOR parameter](optimal-sor-parameter.md)

## Related topics

- [Convergence of the Jacobi method](../../../LinearAlgebra/matrix-decompositions/jacobi-method/README.md): the Jacobi iteration for strictly diagonally dominant matrices.
- [Conjugate gradient method](../../../LinearAlgebra/matrix-decompositions/conjugate-gradient-method/README.md) and [GMRES](../../../LinearAlgebra/matrix-decompositions/gmres/README.md): Krylov methods, which accelerate such iterations.
- [Spectral radius formula in a complex Banach algebra](../../operator-algebras/spectral-radius-formula.md)
