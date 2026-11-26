# Multivariate Laplace prior as a normal scale mixture

Let $T \ge 1$ be the number of traits and $\Sigma$ a $T \times T$ positive definite scale matrix. The zero-mean multivariate Laplace (MLAP) distribution on $\mathbb{R}^T$ has density

$$p(\beta \mid \Sigma) = \frac{T\,\Gamma(T/2)}{|\Sigma|^{1/2}\,\pi^{T/2}\,\Gamma(1+T)\,2^{1+T}}\,\exp\!\left(-\tfrac12\sqrt{\beta^\top\Sigma^{-1}\beta}\right).$$

**Statement.**

1. If $v^2 \sim \mathrm{Gamma}\big(\text{shape } \tfrac{T+1}{2},\ \text{rate } \tfrac18\big)$ and $\beta \mid v^2 \sim N_T(0, v^2\Sigma)$, then $\beta$ has the MLAP density above.
2. $\mathbb{E}[\beta] = 0$ and $\operatorname{Var}(\beta \mid \Sigma) = 4(T+1)\,\Sigma$.
3. For $T = 1$ the density is $\frac{1}{2\sqrt{4\Sigma}}\exp\!\big(-|\beta|/\sqrt{4\Sigma}\big)$, the double-exponential (Laplace) law with variance $8\Sigma$, the prior of the single-trait Bayesian LASSO.

The density has contours $\beta^\top\Sigma^{-1}\beta = \text{const}$ (elliptical) and a cusp at the origin, so a marker's vector of effects across traits is shrunk toward zero jointly, more strongly when its Mahalanobis distance from the origin is small. Assigning independent MLAP priors to the effect vectors of all markers defines the multiple-trait Bayesian LASSO.

## Depends on

- [BayesA and BayesB marker-effect priors](bayes-a-and-bayes-b-priors.md)

## Proof depends on

- [Euler's gamma integral](../../../Probability/distributions/continuous/gamma-distribution/gamma-moments/lintegral-rpow-mul-exp-neg-mul-ioi.md)
- [Multivariate Gaussian density function](../../../Probability/distributions/continuous/multivariate-normal-distribution/gaussian-density/multivariate-gaussian-pdfreal.md)

## Expansion

With $q = \beta^\top\Sigma^{-1}\beta$, the mixture density is proportional to $\int_0^\infty (v^2)^{-1/2}\exp\!\big(-q/(2v^2) - v^2/8\big)\,dv^2$, and the identity $\int_0^\infty x^{-1/2}e^{-a/x - bx}\,dx = \sqrt{\pi/b}\,e^{-2\sqrt{ab}}$ with $a = q/2$, $b = 1/8$ gives a multiple of $e^{-\sqrt q/2}$. The constant follows from $\int_{\mathbb{R}^T} e^{-|z|/2}dz = \frac{2\pi^{T/2}}{\Gamma(T/2)}\Gamma(T)\,2^T$ and $\Gamma(1+T) = T\,\Gamma(T)$. The variance is $\mathbb{E}[v^2]\,\Sigma$ with $\mathbb{E}[v^2] = 8\cdot\frac{T+1}{2}$.

## Sources

- D. Gianola and R. L. Fernando, "A multiple-trait Bayesian Lasso for genome-enabled analysis and prediction of complex traits", Genetics 214 (2020), section "Multivariate Laplace prior distribution for marker effects", Equations (7)–(13), <https://doi.org/10.1534/genetics.119.302934> (PMC7017027).
