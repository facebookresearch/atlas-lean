# Negative binomial regression log-likelihood

For a known shape $\theta$, a design $X$, offset $o$ and responses $y$, the negative binomial log-link log-likelihood (up to a term free of $\beta$) is $\ell(\beta) = \sum_i\big(y_i\eta_i - (y_i + \theta)\log(\theta + e^{\eta_i})\big)$ with $\eta(\beta) = X\beta + o$.
