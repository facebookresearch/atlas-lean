# Joint negative binomial regression log-likelihood

For a design $X$, offset $o$ and counts $y$, the joint log-likelihood in $(\beta, \theta)$ is $\sum_i\big(\sum_{j<y_i}\log(\theta + j) - \log y_i! + \theta\log\theta + y_i\eta_i - (y_i + \theta)\log(\theta + e^{\eta_i})\big)$ with $\eta = X\beta + o$; for $\theta > 0$ it is $\sum_i\log\mathrm{NB}(y_i; \theta, e^{\eta_i})$.
