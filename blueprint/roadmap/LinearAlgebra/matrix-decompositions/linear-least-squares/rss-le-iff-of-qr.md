# Least squares via QR factorization

Let $X = QR$ where $X$ and $Q$ are real $m \times k$ matrices with $Q^{\mathsf{T}} Q = I_k$
and $R$ is an invertible $k \times k$ matrix. Then $\theta_0$ minimizes the residual sum of squares
$\|y - X\theta\|_2^2$ if and only if $R\theta_0 = Q^{\mathsf{T}} y$. This is how least-squares
problems are solved in practice: one triangular solve after a QR factorization, which avoids
forming $X^{\mathsf{T}}X$, whose condition number is the square of that of $X$.

## Informally uses

- [Least squares and the normal equations](../../../ComputerScience/machine-learning/supervised-learning/least-squares-ridge-and-lasso-regression/rss-le-iff-normal.md): minimizers are the solutions of the normal equations.

## Related topics

- [Existence of the reduced QR factorization](../qr-factorization/exists-qr.md): a factorization as in the hypothesis, with $R$ upper triangular with positive diagonal, exists whenever the columns of $X$ are linearly independent.

## Sources

- L. N. Trefethen and D. Bau III, Numerical Linear Algebra, SIAM (1997), Lecture 11 (least squares via QR).
