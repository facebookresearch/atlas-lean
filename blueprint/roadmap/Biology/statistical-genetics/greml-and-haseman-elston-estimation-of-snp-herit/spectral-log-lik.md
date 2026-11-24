# Spectral REML criterion for GREML variance components

For a finite index set $r$, real vectors $d, w \in \mathbb{R}^r$ (contrast eigenvalues and rotated
contrasts) and $\theta = (\sigma_g^2, \sigma_e^2) \in \mathbb{R}^2$, with the
[contrast variances](contrast-var.md) $\lambda_i(\theta) = \sigma_g^2 d_i + \sigma_e^2$,

$$\ell(\theta) = -\frac{|r|}{2} \log(2\pi) - \frac12 \sum_{i \in r} \log \lambda_i(\theta) -
\frac12 \sum_{i \in r} \frac{w_i^2}{\lambda_i(\theta)}.$$

The formula is evaluated at every real $\theta$, with the conventions $\log 0 = 0$,
$\log x = \log|x|$ for $x < 0$ and $x/0 = 0$: an index with $\lambda_i(\theta) = 0$ contributes
$0$, and one with $\lambda_i(\theta) < 0$ contributes
$-\frac12 \log|\lambda_i(\theta)| - w_i^2 / (2\lambda_i(\theta))$. Its reading as a
log-likelihood needs every $\lambda_i(\theta) > 0$: there it is the log-density at $w$ of
independent coordinates $w_i \sim N(0, \lambda_i(\theta))$, and it equals the GREML restricted
log-likelihood for an orthonormal contrast that diagonalizes the relationship matrix
([spectral form](reml-log-lik-greml-cov.md)).
