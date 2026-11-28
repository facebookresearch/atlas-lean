# Ordinary least-squares estimator

The ordinary least-squares estimate of $\beta$ in the linear model $y = X\beta + \varepsilon$ is
$\hat\beta = (X^\top X)^{-1} X^\top y$, where the inverse of a singular matrix is taken to be $0$. So
$\hat\beta$ is defined for every design matrix $X$, and $\hat\beta = 0$ when $X^\top X$ is singular. When
$X^\top X$ is invertible, it is the usual least-squares estimate.
