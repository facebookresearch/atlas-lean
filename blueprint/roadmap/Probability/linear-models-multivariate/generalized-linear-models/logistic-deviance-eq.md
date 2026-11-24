# Logistic deviance for binary responses

For an $n \times p$ design $X$, offset $o$, responses $y \in \mathbb{R}^n$ and $\eta(\beta) = X\beta + o$, let $\ell(\beta) = \sum_i\big(y_i\eta_i(\beta) - \log(1 + e^{\eta_i(\beta)})\big)$ be the logistic regression log-likelihood and $\sigma(t) = 1/(1 + e^{-t})$. If every $y_i \in \{0, 1\}$, the logistic deviance equals $-2\ell(\beta)$.
