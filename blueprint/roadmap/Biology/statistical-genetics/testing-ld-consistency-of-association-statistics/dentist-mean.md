# Mean of the standardized DENTIST difference

For real numbers $\rho$ (the true correlation), $r$ (the reference correlation) and $\lambda$ (the mean of the lead variant's $z$-score), put

$$m(\rho, r, \lambda) = \frac{(\rho - r) \lambda}{\sqrt{1 - r^2}},$$

with the conventions $\sqrt{x} = 0$ for $x < 0$ and $x/0 = 0$. When $r^2 < 1$ and $(z_i, z_c)$ is Gaussian with unit variances, covariance $\rho$ and means $\rho\lambda$ and $\lambda$, it is the mean of the standardized difference $(z_i - r z_c)/\sqrt{1 - r^2}$ ([exact law](map-standardized-eq-gaussian-real.md)).
