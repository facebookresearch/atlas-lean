# Generalized least-squares estimator

For a real $n \times p$ design matrix $X$, a noise covariance $V$ and $y \in \mathbb{R}^n$, the generalized least-squares estimate is

$$\hat\beta(y) = (X^\top V^{-1}X)^{-1}X^\top V^{-1}y,$$

with matrix inverses (zero when singular).
