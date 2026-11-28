# No root of the negative binomial score equation for all-zero counts

For a shape $\theta > 0$, a design $X$, offset $o$, responses $y$ and $\eta(\beta) = X\beta + o$, let $\ell(\beta) = \sum_i\big(y_i\eta_i - (y_i + \theta)\log(\theta + e^{\eta_i})\big)$ be the negative binomial log-link log-likelihood (up to a term free of $\beta$) and $s_i = \theta(y_i - e^{\eta_i})/(\theta + e^{\eta_i})$. If every count is $0$ and some column $j$ of $X$ has nonnegative entries, not all zero (an intercept, say), then component $j$ of the score vector is negative at every $\beta$.
