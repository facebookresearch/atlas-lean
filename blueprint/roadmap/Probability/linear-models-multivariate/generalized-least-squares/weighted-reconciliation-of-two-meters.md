# Weighted reconciliation of two meters

Let two meters $y_i = \theta + e_i$ ($i = 1, 2$) measure one conserved flow $\theta \in \mathbb{R}$, with square-integrable errors,
$E e_i = 0$, $\operatorname{Var} e_i = \sigma_i^2 > 0$ and $\operatorname{Cov}(e_1, e_2) = 0$. This is the linear model with design
$X = (1, 1)^{\mathsf T}$ and error covariance $V = \operatorname{diag}(\sigma_1^2, \sigma_2^2)$, whose generalized least-squares
estimate is

$$\hat x = \frac{\sigma_2^2\,y_1 + \sigma_1^2\,y_2}{\sigma_1^2 + \sigma_2^2}.$$

It is the unique minimizer of $(y_1 - x)^2/\sigma_1^2 + (y_2 - x)^2/\sigma_2^2$, it is unbiased, its variance is
$(X^{\mathsf T} V^{-1} X)^{-1} = \sigma_1^2\sigma_2^2/(\sigma_1^2 + \sigma_2^2) \le \min(\sigma_1^2, \sigma_2^2)$, and it has the least
variance among linear unbiased estimates. With a biased meter, $E e_1 = \beta \ne 0$, the estimate has bias
$\sigma_2^2 \beta/(\sigma_1^2 + \sigma_2^2)$; with correlated errors the variance formula fails: for $\sigma_1^2 = 1$, $\sigma_2^2 = 4$ and
$e_2 = 2e_1$ the variance is $36/25$ rather than $4/5$.

## Depends on

- [Generalized least-squares matrix](gls-matrix.md)

## Proof depends on

- [Unbiasedness of the generalized least-squares estimator](gls-matrix-mul-self.md)
- [Covariance of the generalized least-squares estimator](gls-matrix-mul-mul-transpose.md)
- [Aitken's theorem](aitken.md), for minimal variance

## Sources

- A. C. Aitken, On least squares and linear combination of observations, *Proc. Roy. Soc. Edinburgh* 55 (1936), 42–48.
