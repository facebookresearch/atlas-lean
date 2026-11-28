# A shape section of the joint log-likelihood

For a design $X$, offset $o$, counts $y$, coefficients $\beta$ and a shape $\theta$, the joint log-likelihood $\ell(\beta, \theta)$ equals the fixed-shape kernel $\sum_i(y_i\eta_i - (y_i + \theta)\log(\theta + e^{\eta_i}))$ plus $\sum_i\big(\sum_{j<y_i}\log(\theta + j) - \log y_i! + \theta\log\theta\big)$, a term free of $\beta$.
