# All-zero counts have no negative binomial maximum-likelihood estimate

For a shape $\theta > 0$, a design $X$, offset $o$, responses $y$ and $\eta(\beta) = X\beta + o$, let $\ell(\beta) = \sum_i\big(y_i\eta_i - (y_i + \theta)\log(\theta + e^{\eta_i})\big)$ be the negative binomial log-link log-likelihood (up to a term free of $\beta$) and $s_i = \theta(y_i - e^{\eta_i})/(\theta + e^{\eta_i})$. If every count is $0$ and some column of $X$ has nonnegative entries, not all zero, then $\ell$ has no maximizer.
