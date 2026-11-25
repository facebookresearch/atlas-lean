# Matrix Gaussian series, Hermitian case

Let $A_0, \dots, A_{N-1}$ be fixed Hermitian $d \times d$ complex matrices, $d \ge 1$, let $\gamma_0, \dots, \gamma_{N-1}$ be independent standard normal variables, $Y = \sum_k \gamma_k A_k$, and let

$$v(Y) = \|\mathbb{E}\,Y^2\| = \Big\|\sum_k A_k^2\Big\| = \lambda_{\max}\Big(\sum_k A_k^2\Big).$$

Then

$$\mathbb{E}\,\lambda_{\max}(Y) \le \sqrt{2 v(Y) \log d} \qquad\text{and}\qquad \mathbb{P}\{\lambda_{\max}(Y) \ge t\} \le d\, e^{-t^2/(2v(Y))} \quad (t \ge 0).$$

When $v(Y) = 0$ (for instance when every $A_k$ is $0$, or $N = 0$) the quotient $t^2/(2v(Y))$ is read
as $0$, and the tail bound is the trivial value $d$. Tropp's theorem also covers Rademacher
coefficients.

## Informally uses

- [Matrix Laplace transform method, upper tail](measure-real-le-lambda-max-le.md): the reduction of the tail to the trace mgf.
- [Matrix Laplace transform method, expectation bound](integral-lambda-max-le.md): the reduction of $\mathbb{E}\lambda_{\max}$ to the trace mgf.
- [Subadditivity of matrix cumulant generating functions](integral-trace-exp-sum-le.md): with the exact Gaussian cgf $\log \mathbb{E}\, e^{\theta\gamma A} = \theta^2 A^2/2$.

## Sources

- J. A. Tropp, An Introduction to Matrix Concentration Inequalities, Found. Trends Mach. Learn. 8 (2015), 1–230, arXiv:1501.01571, Theorem 4.6.1, displays (4.6.2) and (4.6.3).
- J. A. Tropp, User-friendly tail bounds for sums of random matrices, Found. Comput. Math. 12 (2012), 389–434, arXiv:1004.4389, Theorem 1.2.
