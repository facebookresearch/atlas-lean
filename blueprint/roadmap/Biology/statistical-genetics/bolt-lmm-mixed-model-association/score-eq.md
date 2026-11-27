# Score at the null generalized least-squares fit

Let $(K, \sigma_g^2, \sigma_e^2)$ be [variance components](model.md) on $n$ individuals with [phenotypic covariance](v.md) $V$, let $X$ be any real $n \times p$ matrix, and let $x, y \in \mathbb{R}^n$. Then

$$x^\top P y = x^\top V^{-1} (y - X\hat\beta),$$

where $P$ is the [residual-forming matrix](proj.md) and $\hat\beta$ the [generalized least-squares estimator](gls.md), both with the convention that the inverse of a singular matrix is $0$.
