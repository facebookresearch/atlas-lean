# Linear least squares

If the columns of a real $m \times k$ matrix $X$ are linearly independent, then for every $y \in \mathbb{R}^m$ there is exactly one $\theta_0 \in \mathbb{R}^k$ minimizing $\|y - X\theta\|_2^2$.

## Idea

The least-squares problem fits a linear model to more observations than unknowns: $X\theta_0$ is the orthogonal projection of $y$ onto the column space of $X$, so the residual $y - X\theta_0$ is orthogonal to every column. With $X = QR$, $Q$ having orthonormal columns, the projection is $QQ^{\mathsf T} y$ and the problem becomes the triangular system $R\theta = Q^{\mathsf T} y$. Independent columns make $R$ invertible and the solution unique: $\theta_0 = R^{-1} Q^{\mathsf T} y$ for the reduced QR factorization $X = QR$. Numerical linear algebra prefers this route to the normal equations $X^{\mathsf T} X \theta = X^{\mathsf T} y$, because forming $X^{\mathsf T} X$ squares the condition number. In statistics this is ordinary linear regression.

## Statements

- [Existence and uniqueness of the least-squares solution](exists-unique-rss-le.md)
- [Least squares via QR factorization](rss-le-iff-of-qr.md): the minimizers characterized through a QR factorization

## Background

- [QR factorization](../qr-factorization/README.md): the second statement characterizes the minimizers through a QR factorization.

## Related topics

- [Least squares, ridge and lasso regression](../../../ComputerScience/machine-learning/supervised-learning/least-squares-ridge-and-lasso-regression/README.md)
- [Tikhonov regularization](../../../Analysis/convex-analysis-and-variations/tikhonov-regularization/README.md)
- [Linear models and multivariate analysis](../../../Probability/linear-models-multivariate/README.md)
- [GMRES iterate](../gmres/is-gmresiterate.md): an application: each GMRES iterate is a least-squares solution over a Krylov space.
