# Generalized least-squares estimator

Let $(K, \sigma_g^2, \sigma_e^2)$ be [variance components](model.md) on $n$ individuals with [phenotypic covariance](v.md) $V$, let $X$ be a real $n \times p$ design matrix and $y \in \mathbb{R}^n$. The generalized least-squares estimator is

$$\hat\beta = (X^\top V^{-1} X)^{-1} X^\top V^{-1} y \in \mathbb{R}^p,$$

with the convention that the inverse of a singular matrix is $0$ (so $\hat\beta = 0$ when $X^\top V^{-1} X$ is singular, in particular when $X$ does not have full column rank).
