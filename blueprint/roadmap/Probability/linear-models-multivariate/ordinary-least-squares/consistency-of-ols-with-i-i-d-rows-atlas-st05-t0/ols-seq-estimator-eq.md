# Least-squares estimator in normalized Gram and score form

Let $(x_i)_{i \ge 0}$ be regressors in $\mathbb{R}^p$ and $(y_i)_{i \ge 0}$ real responses. For every sample size $n$ and outcome $\omega$, the least-squares estimator from the first $n$ observations satisfies

$$\hat\beta_n = \Big(\frac{1}{n}\sum_{i<n} x_i x_i^\top\Big)^{-1}\Big(\frac{1}{n}\sum_{i<n} y_i\, x_i\Big),$$

where the inverse of a singular matrix is taken to be the zero matrix and $1/0 = 0$; the identity holds for every $n$, including $n = 0$ and a singular sample Gram matrix.
