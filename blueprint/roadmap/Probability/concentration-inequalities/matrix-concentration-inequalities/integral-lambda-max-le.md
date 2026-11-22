# Matrix Laplace transform method, expectation bound

Let $Y$ be a random Hermitian $d \times d$ matrix on a probability space, with $d \ge 1$, such that $\lambda_{\max}(Y)$ is integrable, and let $\theta > 0$ be such that $\operatorname{tr} e^{\theta Y}$ is integrable. Then

$$\mathbb{E}\,\lambda_{\max}(Y) \le \frac{1}{\theta}\log \mathbb{E}\operatorname{tr} e^{\theta Y}.$$

The proof applies Jensen's inequality to the exponential, $e^{\theta\,\mathbb{E}\lambda_{\max}(Y)} \le \mathbb{E}\, e^{\theta\lambda_{\max}(Y)}$, then the trace bound, then the logarithm. Tropp remarks that this argument has no perfect scalar analogue.

## Informally uses

- [Trace exponential dominates the top eigenvalue](../../../LinearAlgebra/eigenvalues-and-canonical-forms/eigenvalues-and-spectral-norm-of-hermitian-matri/exp-mul-lambda-max-le-re-trace-exp.md): the matrix step $e^{\theta\lambda_{\max}(Y)} \le \operatorname{tr} e^{\theta Y}$.

## Sources

- J. A. Tropp, An Introduction to Matrix Concentration Inequalities, Found. Trends Mach. Learn. 8 (2015), 1–230, arXiv:1501.01571, Proposition 3.2.2, display (3.2.4).
