# Uniqueness of the logistic maximum-likelihood estimate

For an $n \times p$ design $X$, offset $o$, responses $y \in \mathbb{R}^n$ and $\eta(\beta) = X\beta + o$, let $\ell(\beta) = \sum_i\big(y_i\eta_i(\beta) - \log(1 + e^{\eta_i(\beta)})\big)$ be the logistic regression log-likelihood and $\sigma(t) = 1/(1 + e^{-t})$. If $X$ has full column rank, $\ell$ has at most one maximizer.
