# Unbiased sample covariance matrix

Let $X$ be a real $n \times p$ data matrix whose rows are observations. With $X_c$ the [column-centered matrix](center.md), the unbiased sample covariance matrix is

$$S = \frac{1}{n - 1}\, X_c^\top X_c.$$

The divisor needs $n \ge 2$; for $n = 1$ the factor $(n-1)^{-1} = 0^{-1}$ is $0$ by convention, so $S = 0$ (and for $n = 0$ the product $X_c^\top X_c$ is the zero matrix).
