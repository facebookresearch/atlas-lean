# Least-squares estimator from the first n observations

Let $(x_i)_{i \ge 0}$ be random regressors in $\mathbb{R}^p$ and $(y_i)_{i \ge 0}$ real responses on a common sample space. At sample size $n$ and outcome $\omega$, the least-squares estimator is

$$\hat\beta_n(\omega) = (X_n^\top X_n)^{-1} X_n^\top Y_n,$$

where $X_n$ is the $n \times p$ matrix with rows $x_0(\omega), \dots, x_{n-1}(\omega)$, $Y_n = (y_0(\omega), \dots, y_{n-1}(\omega))$, and the inverse of a singular matrix is taken to be the zero matrix.
