# Residual-maker matrix

The residual-maker matrix of a design matrix $X$ is $M = I - X (X^\top X)^{-1} X^\top$, where the
inverse of a singular matrix is taken to be $0$, so $M = I$ when $X^\top X$ is singular. Applied to
observations $y$, it gives $M y = y - X\hat\beta$ for the
[ordinary least-squares estimate](ols-estimator.md) $\hat\beta$; these are the least-squares residuals
when $X^\top X$ is invertible.
