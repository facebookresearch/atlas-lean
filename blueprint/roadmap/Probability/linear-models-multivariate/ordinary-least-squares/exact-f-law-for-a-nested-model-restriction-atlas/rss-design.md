# Residual sum of squares of a design

Let $X$ be a real $n \times p$ design matrix (rows and columns indexed by finite sets of sizes $n$ and $p$) and $y \in \mathbb{R}^n$, and let $\hat\beta = (X^\top X)^{-1} X^\top y$ be the least-squares estimator, where the inverse of a singular matrix is taken to be the zero matrix. The residual sum of squares of the design $X$ at $y$ is $\mathrm{RSS}(X, y) = \|y - X\hat\beta\|^2$.
