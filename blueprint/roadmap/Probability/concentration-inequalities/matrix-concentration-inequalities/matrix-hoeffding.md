# Matrix Hoeffding inequality

Let $X_0, \dots, X_{N-1}$ be independent random Hermitian $d \times d$ complex matrices on a probability space, $d \ge 1$, and $A_0, \dots, A_{N-1}$ fixed Hermitian matrices, such that

$$\mathbb{E}\,X_k = 0 \quad\text{and}\quad X_k^2 \preceq A_k^2 \qquad\text{for each } k,$$

the semidefinite bound holding for every outcome. Let $\sigma^2 = \|\sum_k A_k^2\| = \lambda_{\max}(\sum_k A_k^2)$. Then for all $t \ge 0$,

$$\mathbb{P}\Big\{\lambda_{\max}\Big(\sum_k X_k\Big) \ge t\Big\} \le d\, e^{-t^2/(8\sigma^2)} .$$

When $\sigma^2 = 0$ the quotient $t^2/(8\sigma^2)$ is read as $0$, and the bound is the trivial value $d$.
Tropp notes that the constant $1/8$ can be improved with more information.

## Informally uses

- [Matrix Laplace transform method, upper tail](measure-real-le-lambda-max-le.md): the reduction of the tail to the trace mgf.
- [Subadditivity of matrix cumulant generating functions](integral-trace-exp-sum-le.md): Lieb's theorem applied summand by summand, as in the source proof.

## Background

- [Two-sided Hoeffding inequality for Bernoulli sums](../hoeffding-s-inequality/hoeffding-bernoulli-sum-abs-tail.md): background, the scalar inequality it extends.

## Sources

- J. A. Tropp, User-friendly tail bounds for sums of random matrices, Found. Comput. Math. 12 (2012), 389–434, arXiv:1004.4389, Theorem 1.3.
