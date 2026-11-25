# Least squares, ridge and lasso regression

- [Residual sum of squares](rss.md)
- [Expansion of the residual sum of squares](rss-add.md)
- [Pythagoras for least squares](rss-eq-of-normal.md)
- [Least squares and the normal equations](rss-le-iff-normal.md)
- [Least-squares estimates exist](exists-normal.md)
- [Closed-form solution of the normal equations](normal-inv.md)
- [Convexity of the residual sum of squares](convex-on-rss.md)
- [Leave-one-out least squares: leverage and deleted residual](leave-one-out-leverage-residual.md)
- [The set of least-squares minimizers](the-set-of-least-squares-minimizers.md)

## Gaussian noise: least squares is maximum likelihood

- [Gaussian likelihood of linear regression](gauss-likelihood.md)
- [The Gaussian likelihood decreases with the residual sum of squares](gauss-likelihood-le-iff.md)
- [Least squares is maximum likelihood](is-max-on-gauss-likelihood-iff.md)
- [Existence of the Gaussian maximum likelihood estimate](exists-is-max-on-gauss-likelihood.md)

## Ridge regression: MAP under a Gaussian prior

- [Ridge objective](ridge.md)
- [Expansion of the ridge objective around a solution of its normal equations](ridge-eq-of-normal.md)
- [Solutions of the ridge normal equations minimize the ridge objective](ridge-le-of-normal.md)
- [The ridge matrix is positive definite](pos-def-ridge.md)
- [Ridge estimate](ridge-estimate.md)
- [Closed form of ridge regression](ridge-le-ridge-estimate.md)
- [Density of independent centred Gaussian coordinates](prod-gaussian-pdfreal-zero.md)
- [Posterior kernel of ridge regression](ridge-posterior.md)
- [Ridge regression is MAP estimation](ridge-posterior-le-iff.md)
- [The ridge estimate maximizes the ridge posterior](is-max-on-ridge-posterior.md)

## Lasso: MAP under a Laplace prior

- [Lasso objective](lasso.md)
- [Laplace density](laplace-pdf.md)
- [Lasso posterior kernel](lasso-posterior.md)
- [Lasso is MAP estimation](lasso-posterior-le-iff.md)
- [Convexity of the lasso objective](convex-on-lasso.md)
- [Soft thresholding](soft-threshold.md)
- [Soft thresholding solves the one-dimensional lasso](soft-threshold-le.md)
- [Lasso with an orthonormal design](lasso-soft-threshold-le.md)

## Related topics

- [Linear least squares](../../../../LinearAlgebra/matrix-decompositions/linear-least-squares/README.md)
- [QR factorization](../../../../LinearAlgebra/matrix-decompositions/qr-factorization/README.md)
- [Tikhonov regularization](../../../../Analysis/convex-analysis-and-variations/tikhonov-regularization/README.md)
- [First-order conditions for convexity and optimality](../../../../Analysis/convex-analysis-and-variations/first-order-conditions-for-convexity/README.md)
- [Gradient descent](../../../../Analysis/convex-analysis-and-variations/gradient-descent/README.md): the convergence rates of first-order methods applied to these convex objectives.
- [Matrix decompositions and linear systems](../../../../LinearAlgebra/matrix-decompositions/README.md)
- [Hilbert projection theorem](../../../../Analysis/hilbert-spaces/hilbert-projection-theorem/README.md): the least-squares fit is the orthogonal projection of the response onto the column space of the design.
- [Singular value decomposition](../../../../LinearAlgebra/matrix-decompositions/singular-value-decomposition/README.md): the closed forms of least squares and ridge regression diagonalize in the singular basis of the design, where ridge shrinks each singular direction.
- [Positive definite matrices and matrix inequalities](../../../../LinearAlgebra/positive-definite-matrices/README.md): the empirical covariance $\hat\Sigma = \frac{1}{n} \Phi^\top \Phi$ is positive semidefinite, and $\hat\Sigma + \lambda I$ positive definite for $\lambda > 0$.
- [Eigenvalues and spectral norm of Hermitian matrices](../../../../LinearAlgebra/eigenvalues-and-canonical-forms/eigenvalues-and-spectral-norm-of-hermitian-matri/README.md): the extreme eigenvalues of $\hat\Sigma$ are the smoothness and strong-convexity constants of the least-squares objective.
- [Generalization bounds and concentration](../../generalization-bounds-and-concentration/README.md): estimation-error bounds for empirical risk minimization.
- [Lasso error bounds under restricted eigenvalues](../../../../Probability/linear-models-multivariate/lasso-error-bounds-under-restricted-eigenvalues/README.md)
- [Sparse recovery by orthogonal matching pursuit](../../../../Analysis/approximation-theory/sparse-recovery-by-orthogonal-matching-pursuit/README.md)
- [Recursive least squares](../../../../Analysis/control-theory/recursive-least-squares/README.md): the same estimates computed one observation at a time by rank-one updates; started at $\theta_0 = 0$, $P_0 = \lambda^{-1} I$ the recursion returns the ridge estimate.
