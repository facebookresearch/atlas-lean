# Linear least squares

Minimizing $\|y - X\theta\|_2$. A solution always exists and the solutions are exactly those of the normal equations $X^{\mathsf{T}}X\theta = X^{\mathsf{T}}y$, the residual being orthogonal to the range of $X$ (Trefethen and Bau, Lecture 11): see [least squares and the normal equations](../../../ComputerScience/machine-learning/supervised-learning/least-squares-ridge-and-lasso-regression/rss-le-iff-normal.md) and [existence of least-squares estimates](../../../ComputerScience/machine-learning/supervised-learning/least-squares-ridge-and-lasso-regression/exists-normal.md), where this is linear regression. With full column rank the solution is unique and numerical linear algebra computes it from a QR factorization, $\theta = R^{-1}Q^{\mathsf{T}}y$ (Trefethen and Bau, Lecture 11), never forming $X^{\mathsf{T}}X$. Ridge regression is the [Tikhonov regularization](../../../Analysis/convex-analysis-and-variations/tikhonov-regularization/README.md) of this problem, and the statistical theory of the estimator (Gauss–Markov, Frisch–Waugh–Lovell, generalized least squares) is in [linear models](../../../Probability/linear-models-multivariate/README.md).

- [Least squares via QR factorization](rss-le-iff-of-qr.md)
- [Existence and uniqueness of the least-squares solution](exists-unique-rss-le.md)

## Related topics

- [QR factorization](../qr-factorization/README.md)
- [Least squares, ridge and lasso regression](../../../ComputerScience/machine-learning/supervised-learning/least-squares-ridge-and-lasso-regression/README.md)
- [Tikhonov regularization](../../../Analysis/convex-analysis-and-variations/tikhonov-regularization/README.md)
- [Linear models and multivariate analysis](../../../Probability/linear-models-multivariate/README.md)
- [GMRES](../gmres/README.md)
