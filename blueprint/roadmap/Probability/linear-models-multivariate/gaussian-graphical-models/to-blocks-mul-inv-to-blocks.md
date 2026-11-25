# The regression coefficient from the precision matrix

Let $\iota, \kappa$ be finite index sets and $S$ a positive definite real matrix on $\iota \sqcup \kappa$ with precision $K = S^{-1}$. Then

$$S_{12} S_{22}^{-1} = -(K_{11})^{-1} K_{12}.$$

This is the coefficient of $y - \mu_Y$ in the conditional mean of $X$ given $Y = y$ for a Gaussian vector $(X, Y) \sim N(\mu, S)$, whose conditional covariance is $(K_{11})^{-1}$ ([the conditional covariance is the inverse of a precision block](inv-to-blocks-inv.md)).
