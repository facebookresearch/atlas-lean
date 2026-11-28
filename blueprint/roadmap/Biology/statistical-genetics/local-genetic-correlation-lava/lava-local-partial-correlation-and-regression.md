# Local multiple regression and partial genetic correlation

Let $\Omega$ be the positive definite local genetic covariance matrix of the genetic components of a set of phenotypes at one locus, as in the [LAVA estimator](lava-method-of-moments-estimator.md). Partition the phenotypes into an outcome $Y$ and predictors $X$, with

$$\Omega = \begin{pmatrix}\Omega_X & \Omega_{XY}\\ \Omega_{XY}^\top & \omega_Y^2\end{pmatrix}.$$

**Multiple regression.** Decompose the genetic component of $Y$ as $G_Y = G_X\gamma^{(u)} + \varepsilon$ with $\operatorname{cov}(G_X, \varepsilon) = 0$. Then

$$\gamma^{(u)} = \Omega_X^{-1}\Omega_{XY}, \qquad \tau_{(u)}^2 = \operatorname{Var}(\varepsilon) = \omega_Y^2 - \Omega_{XY}^\top\Omega_X^{-1}\Omega_{XY}.$$

With $\vec\omega_X$ the vector of standard deviations of the predictors, the standardized coefficients are $\gamma = \operatorname{diag}(\vec\omega_X)\,\gamma^{(u)}/\omega_Y$, the standardized residual variance is $\tau^2 = \tau_{(u)}^2/\omega_Y^2$, and the local genetic variance of $Y$ explained by $X$ is $r^2 = 1 - \tau^2$.

**Partial correlation.** For phenotypes $X$ and $Y$ and a conditioning set $Z$, the partial genetic covariance and variances are

$$\omega_{XY\mid Z} = \omega_{XY} - \Omega_{XZ}\Omega_Z^{-1}\Omega_{ZY}, \qquad \omega_{X\mid Z}^2 = \omega_X^2 - \Omega_{XZ}\Omega_Z^{-1}\Omega_{ZX},$$

and likewise for $Y$, and the local partial genetic correlation is

$$\rho_{XY\mid Z} = \frac{\omega_{XY\mid Z}}{\sqrt{\omega_{X\mid Z}^2\,\omega_{Y\mid Z}^2}},$$

the correlation of the residuals of $G_X$ and $G_Y$ after linear regression on $G_Z$. All quantities are estimated by substituting $\hat\Omega$; their sampling distributions have no closed form and are obtained by simulation from the noncentral Wishart law of $\hat\delta^\top\hat\delta$.

## Depends on

- [LAVA method-of-moments estimator of the local genetic covariance](lava-method-of-moments-estimator.md)

## Expansion

These are the population least-squares (linear projection) formulas for a random vector with covariance $\Omega$: the normal equations $\operatorname{cov}(G_X, G_Y - G_X\gamma) = 0$ give $\Omega_X\gamma^{(u)} = \Omega_{XY}$, and the residual variance is the Schur complement of $\Omega_X$. Partial covariances are the corresponding Schur complements for the pair $(X, Y)$ given $Z$.

## Sources

- J. Werme, S. van der Sluis, D. Posthuma and C. A. de Leeuw, "An integrated framework for local genetic correlation analysis", Nature Genetics 54 (2022), 274–282, Methods, "Local multiple regression & partial correlations", <https://doi.org/10.1038/s41588-022-01017-y>.
