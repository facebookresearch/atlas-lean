# REML score for the genetic variance in spectral form

For a finite index set $r$, real vectors $d, w \in \mathbb{R}^r$ and
$\theta = (\sigma_g^2, \sigma_e^2) \in \mathbb{R}^2$, with the
[contrast variances](contrast-var.md) $\lambda_i(\theta) = \sigma_g^2 d_i + \sigma_e^2$,

$$U_g(\theta) = \frac12 \sum_{i \in r}
\frac{d_i \, (w_i^2 - \lambda_i(\theta))}{\lambda_i(\theta)^2},$$

with the convention $x / 0 = 0$: an index with $\lambda_i(\theta) = 0$ contributes $0$. Its reading
as the REML score needs every $\lambda_i(\theta) > 0$: there it is the partial derivative in
$\sigma_g^2$ of the [spectral REML criterion](spectral-log-lik.md)
([derivative](has-deriv-at-spectral-log-lik-fst.md)).
