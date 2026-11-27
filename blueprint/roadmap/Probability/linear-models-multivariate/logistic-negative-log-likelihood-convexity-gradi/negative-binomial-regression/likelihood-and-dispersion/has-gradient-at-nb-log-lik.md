# Gradient of the negative binomial regression log-likelihood

For a shape $\theta > 0$, a design $X$, offset $o$, responses $y$ and $\eta(\beta) = X\beta + o$, let $\ell(\beta) = \sum_i\big(y_i\eta_i - (y_i + \theta)\log(\theta + e^{\eta_i})\big)$ be the negative binomial log-link log-likelihood (up to a term free of $\beta$) and $s_i = \theta(y_i - e^{\eta_i})/(\theta + e^{\eta_i})$. Then at every $\beta$, the Euclidean gradient of $\ell$ is $X^\top s(\beta)$.
