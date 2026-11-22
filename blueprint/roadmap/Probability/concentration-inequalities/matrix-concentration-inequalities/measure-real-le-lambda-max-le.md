# Matrix Laplace transform method, upper tail

Let $Y$ be a random Hermitian $d \times d$ matrix on a finite measure space $(\Omega, \mu)$, with $d \ge 1$, and let $\theta > 0$ be such that $\omega \mapsto \operatorname{tr} e^{\theta Y(\omega)}$ is integrable. Then for every real $t$,

$$\mu\{\lambda_{\max}(Y) \ge t\} \le e^{-\theta t} \int \operatorname{tr} e^{\theta Y}\, d\mu .$$

Since the bound holds for every $\theta > 0$, it holds for the infimum over $\theta > 0$, which is the form of Tropp's Proposition 3.2.1. The proof is Markov's inequality applied to $e^{\theta\lambda_{\max}(Y)}$, followed by $e^{\theta\lambda_{\max}(Y)} \le \operatorname{tr} e^{\theta Y}$.

## Informally uses

- [Trace exponential dominates the top eigenvalue](../../../LinearAlgebra/eigenvalues-and-canonical-forms/eigenvalues-and-spectral-norm-of-hermitian-matri/exp-mul-lambda-max-le-re-trace-exp.md): the matrix step $e^{\theta\lambda_{\max}(Y)} \le \operatorname{tr} e^{\theta Y}$.

## Background

- [Fixed-direction Chernoff bound](../../large-deviations/cram-r-s-theorem/cramer-upper-bound.md): background, the scalar (vector-valued, fixed direction) Laplace transform method this generalizes.

## Sources

- J. A. Tropp, An Introduction to Matrix Concentration Inequalities, Found. Trends Mach. Learn. 8 (2015), 1–230, arXiv:1501.01571, Proposition 3.2.1, display (3.2.1).
- J. A. Tropp, User-friendly tail bounds for sums of random matrices, Found. Comput. Math. 12 (2012), 389–434, arXiv:1004.4389, Proposition 3.1.
- R. Ahlswede and A. Winter, Strong converse for identification via quantum channels, IEEE Trans. Inform. Theory 48 (2002), 569–579 (a version of the method; the statement in this form is from R. I. Oliveira, 2010, per Tropp's §3.7.1).
