# Matrix Chernoff inequality

Let $X_0, \dots, X_{N-1}$ be independent random Hermitian $d \times d$ complex matrices on a probability space, $d \ge 1$, with

$$0 \le \lambda_{\min}(X_k) \quad\text{and}\quad \lambda_{\max}(X_k) \le L \qquad\text{for each } k,$$

where $L > 0$. Let $Y = \sum_k X_k$, $\mu_{\min} = \lambda_{\min}(\mathbb{E}\,Y)$ and $\mu_{\max} = \lambda_{\max}(\mathbb{E}\,Y)$. Then

$$\mathbb{P}\{\lambda_{\max}(Y) \ge (1+\varepsilon)\mu_{\max}\} \le d\left[\frac{e^{\varepsilon}}{(1+\varepsilon)^{1+\varepsilon}}\right]^{\mu_{\max}/L} \quad (\varepsilon \ge 0),$$

$$\mathbb{P}\{\lambda_{\min}(Y) \le (1-\varepsilon)\mu_{\min}\} \le d\left[\frac{e^{-\varepsilon}}{(1-\varepsilon)^{1-\varepsilon}}\right]^{\mu_{\min}/L} \quad (0 \le \varepsilon < 1).$$

These are the scalar Chernoff bounds for sums of bounded nonnegative variables, up to the dimensional factor $d$. Typical uses: the smallest singular value of a random submatrix, sparsification of graphs and random sampling of columns.

The bounds are required for every outcome, and the hermiticity of $\sum_k X_k$ and of $\mathbb{E}\,Y$ is taken as a hypothesis (both always hold).

## Informally uses

- [Matrix Laplace transform method, upper tail](measure-real-le-lambda-max-le.md): the reduction of the upper tail to the trace mgf.
- [Matrix Laplace transform method, lower tail](measure-real-lambda-min-le-le.md): the reduction of the lower tail to the trace mgf.
- [Subadditivity of matrix cumulant generating functions](integral-trace-exp-sum-le.md): the trace mgf of the sum is controlled by the summands' cgfs.

## Sources

- J. A. Tropp, An Introduction to Matrix Concentration Inequalities, Found. Trends Mach. Learn. 8 (2015), 1–230, arXiv:1501.01571, Theorem 5.1.1, displays (5.1.5) and (5.1.6).
- J. A. Tropp, User-friendly tail bounds for sums of random matrices, Found. Comput. Math. 12 (2012), 389–434, arXiv:1004.4389, Theorem 1.1.
