# Residual-forming matrix

Let $(K, \sigma_g^2, \sigma_e^2)$ be [variance components](model.md) on $n$ individuals with [phenotypic covariance](v.md) $V$, and let $X$ be a real $n \times p$ matrix. The residual-forming matrix is the $n \times n$ matrix

$$P = V^{-1} - V^{-1} X (X^\top V^{-1} X)^{-1} X^\top V^{-1},$$

with the convention that the inverse of a singular matrix is $0$ (so $P = V^{-1}$ when $X^\top V^{-1} X$ is singular).
