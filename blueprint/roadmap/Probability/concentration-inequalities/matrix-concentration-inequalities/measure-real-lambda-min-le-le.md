# Matrix Laplace transform method, lower tail

Let $Y$ be a random Hermitian $d \times d$ matrix on a finite measure space $(\Omega, \mu)$, with $d \ge 1$, and let $\theta < 0$ be such that $\omega \mapsto \operatorname{tr} e^{\theta Y(\omega)}$ is integrable. Then for every real $t$,

$$\mu\{\lambda_{\min}(Y) \le t\} \le e^{-\theta t} \int \operatorname{tr} e^{\theta Y}\, d\mu .$$

## Informally uses

- [Trace exponential dominates the bottom eigenvalue](../../../LinearAlgebra/eigenvalues-and-canonical-forms/eigenvalues-and-spectral-norm-of-hermitian-matri/exp-mul-lambda-min-le-re-trace-exp.md): the matrix step for $\theta < 0$.

## Sources

- J. A. Tropp, An Introduction to Matrix Concentration Inequalities, Found. Trends Mach. Learn. 8 (2015), 1–230, arXiv:1501.01571, Proposition 3.2.1, display (3.2.2).
