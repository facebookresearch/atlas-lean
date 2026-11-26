# HC0 sandwich covariance estimator for least squares

Let $(x_i)_{i \ge 0}$ be regressors in $\mathbb{R}^p$ and $(y_i)_{i \ge 0}$ real responses. At sample size $n$, let $\hat\beta_n$ be the least-squares estimator from the first $n$ observations, $\hat u_i = y_i - x_i^\top\hat\beta_n$ the residuals, $\hat Q_n = \frac1n\sum_{i<n} x_i x_i^\top$ the sample Gram matrix and $\hat\Omega_n = \frac1n\sum_{i<n} \hat u_i^2\, x_i x_i^\top$ the HC0 meat. The HC0 sandwich is

$$\hat V_n = \hat Q_n^{-1}\, \hat\Omega_n\, \big(\hat Q_n^{-1}\big)^\top,$$

where the inverse of a singular matrix is taken to be the zero matrix and $1/0 = 0$.
