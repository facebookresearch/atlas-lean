# Hoffman–Wielandt inequality

Let $A$ and $B$ be Hermitian $n \times n$ complex matrices with eigenvalues $\lambda_1 \ge \dots \ge \lambda_n$ and $\mu_1 \ge \dots \ge \mu_n$, counted with multiplicity. Then

$$\sum_{i=1}^n (\lambda_i - \mu_i)^2 \le \sum_{i,j=1}^n |A_{ij} - B_{ij}|^2,$$

the squared Frobenius norm of $A - B$.

## Idea

Eigenvalues of Hermitian matrices are stable under perturbation, and in the Frobenius norm the bound is as clean as possible: the sorted spectra are at least as close, in Euclidean distance, as the matrices themselves. Expanding the Frobenius norm of $A - B$ in eigenbases reduces the inequality to $\operatorname{tr}(AB) \le \sum_i \lambda_i \mu_i$, which is von Neumann's trace inequality. Hoffman and Wielandt proved it in 1953 for normal matrices, with a best pairing of the eigenvalues. As a consequence, linear statistics $\sum_i f(\lambda_i)$ of the spectrum with Lipschitz $f$ change little when the matrix changes little, a fact used throughout random matrix theory.

## Statements

- [Hoffman–Wielandt inequality for Hermitian matrices](hoffman-wielandt-hermitian.md)
- [Lipschitz linear statistics of Hermitian spectra are stable](abs-sum-sub-sum-le-of-lipschitz-with.md): consequence: Lipschitz linear statistics of the spectrum are stable
