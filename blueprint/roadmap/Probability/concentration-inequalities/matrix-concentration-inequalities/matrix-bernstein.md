# Matrix Bernstein inequality, Hermitian case

Let $X_0, \dots, X_{N-1}$ be independent random Hermitian $d \times d$ complex matrices on a probability space, $d \ge 1$, with

$$\mathbb{E}\,X_k = 0 \quad\text{and}\quad \lambda_{\max}(X_k) \le L \qquad\text{for each } k, \text{ where } L \ge 0,$$

with integrable entries of $X_k$ and $X_k^2$. Let $Y = \sum_k X_k$ and let

$$v(Y) = \|\mathbb{E}\,Y^2\| = \Big\|\sum_k \mathbb{E}\,X_k^2\Big\| = \lambda_{\max}\Big(\sum_k \mathbb{E}\,X_k^2\Big)$$

be the matrix variance statistic (the matrix is positive semidefinite, so its norm is its largest eigenvalue). Then for all $t \ge 0$,

$$\mathbb{P}\{\lambda_{\max}(Y) \ge t\} \le d \cdot \exp\left(\frac{-t^2/2}{v(Y) + Lt/3}\right),$$

where the quotient is read as $0$ when $v(Y) + Lt/3 = 0$, giving the trivial value $d$.

The rectangular version (Tropp's Theorem 6.1.1, with $d_1 + d_2$ in place of $d$) follows through the Hermitian dilation.

## Informally uses

- [Matrix Laplace transform method, upper tail](measure-real-le-lambda-max-le.md): the reduction of the tail to the trace mgf.
- [Subadditivity of matrix cumulant generating functions](integral-trace-exp-sum-le.md): the trace mgf of the sum is controlled by the summands' cgfs.

## Background

- [Hermitian dilation](../../../LinearAlgebra/eigenvalues-and-canonical-forms/eigenvalues-and-spectral-norm-of-hermitian-matri/dilation.md): background, the dilation through which the rectangular version follows.
- [Two-sided Hoeffding inequality for Bernoulli sums](../hoeffding-s-inequality/hoeffding-bernoulli-sum-abs-tail.md): background, the scalar exponential tail bound for bounded independent summands.

## Sources

- J. A. Tropp, An Introduction to Matrix Concentration Inequalities, Found. Trends Mach. Learn. 8 (2015), 1–230, arXiv:1501.01571, Theorem 6.6.1, display (6.6.3).
- J. A. Tropp, User-friendly tail bounds for sums of random matrices, Found. Comput. Math. 12 (2012), 389–434, arXiv:1004.4389, Theorem 1.4.
