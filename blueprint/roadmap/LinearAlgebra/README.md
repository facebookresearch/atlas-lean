# Linear Algebra

Linear algebra studies vector spaces, linear maps, matrices, duality, dimension, and spectral structure.

The largest field, [special matrices](special-matrices/README.md), a third of the subject, covers circulant matrices,
total positivity, the [Perron–Frobenius theorem](special-matrices/perron-frobenius-theorem/README.md) for irreducible
nonnegative matrices and van der Waerden's lower bound $n!/n^n$ for the permanent of a doubly stochastic $n \times n$
matrix. [Matrix decompositions](matrix-decompositions/README.md) and linear systems include the
[conjugate gradient method](matrix-decompositions/conjugate-gradient-method/README.md), whose energy-norm error after
$k$ steps is at most $2\big((\sqrt{\kappa} - 1)/(\sqrt{\kappa} + 1)\big)^k$ times the initial one, $\kappa$ being the
condition number of the positive definite matrix.
[Eigenvalues and canonical forms](eigenvalues-and-canonical-forms/README.md) include the Jordan normal form of a
matrix whose characteristic polynomial splits, and [positive definite matrices](positive-definite-matrices/README.md)
come with Hadamard's inequality and von Neumann's trace inequality.

Numerical linear algebra in the sense of Trefethen and Bau sits under matrix decompositions: the [QR factorization](matrix-decompositions/qr-factorization/README.md), [linear least squares](matrix-decompositions/linear-least-squares/README.md), the [singular value decomposition](matrix-decompositions/singular-value-decomposition/README.md) with the perfect conditioning of singular values, and the Krylov methods ([Arnoldi and Lanczos](matrix-decompositions/arnoldi-and-lanczos-iterations/README.md), [GMRES](matrix-decompositions/gmres/README.md), conjugate gradients), whose convergence is a problem of polynomial approximation solved by [Chebyshev polynomials](../Analysis/approximation-theory/minimax-property-of-the-chebyshev-polynomials/README.md). This is also the linear algebra on which machine learning rests: least squares is [linear regression](../ComputerScience/machine-learning/supervised-learning/least-squares-ridge-and-lasso-regression/README.md) and its Tikhonov regularization is ridge regression, the truncated SVD (Eckart–Young) is [principal component analysis](../Probability/linear-models-multivariate/principal-component-analysis/README.md) and low-rank approximation, and the spectral norm and its dual, the nuclear norm, drive [matrix-aware optimizers](../ComputerScience/machine-learning/supervised-learning/matrix-aware-optimizers/README.md).

The accuracy and cost of these algorithms are analysed in three steps. [Perturbation theory](matrix-decompositions/perturbation-theory-for-linear-systems/README.md) measures the sensitivity of the problem by the condition number $\kappa(A) = \|A\|\,\|A^{-1}\|$, which bounds the relative change of the solution of $Ax = b$ under relative changes of $A$ and $b$ and is the reciprocal of the relative distance to the singular matrices. [Rounding error analysis](../ComputerScience/algebraic-and-numerical-algorithms/rounding-error-analysis/README.md) shows that an algorithm is backward stable, as Gaussian elimination is when $|\hat L|\,|\hat U|$ stays comparable to $A$; error is then at most about condition number times backward error. Finally, [communication lower bounds](../ComputerScience/algebraic-and-numerical-algorithms/communication-lower-bounds/README.md) show that classical matrix multiplication and the factorizations built on it must move $\Omega(n^3/\sqrt{M})$ words through a fast memory of $M$ words, a consequence of the [Loomis–Whitney inequality](../Combinatorics/extremal-set-theory/loomis-whitney-and-brascamp-lieb-inequalities/README.md). For nonsymmetric eigenvalue problems the [Bauer–Fike theorem](../Analysis/operator-theory/eigenvalue-inequalities/bauer-fike-theorem/README.md) plays the role of the condition number bound.

- [Bases and dimension](bases-and-dimension/README.md)
- [Linear maps and duality](linear-maps-and-duality/README.md)
- [Matrices and matrix algebra](matrix-algebra/README.md)
- [Eigenvalues and canonical forms](eigenvalues-and-canonical-forms/README.md)
- [Matrix decompositions and linear systems](matrix-decompositions/README.md)
- [Determinants and matrix identities](determinants-and-matrix-identities/README.md)
- [Positive definite matrices and matrix inequalities](positive-definite-matrices/README.md)
- [Bilinear and quadratic forms](bilinear-and-quadratic-forms/README.md)
- [Special matrices](special-matrices/README.md)
- [Not yet classified](not-yet-classified/README.md)
