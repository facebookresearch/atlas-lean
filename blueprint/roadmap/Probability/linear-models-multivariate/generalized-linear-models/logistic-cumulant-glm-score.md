# Logistic regression score

For an $n \times p$ design $X$, offset $o$, responses $y \in \mathbb{R}^n$ and $\eta(\beta) = X\beta + o$, let $\ell(\beta) = \sum_i\big(y_i\eta_i(\beta) - \log(1 + e^{\eta_i(\beta)})\big)$ be the logistic regression log-likelihood and $\sigma(t) = 1/(1 + e^{-t})$. Then the canonical-link score of the Bernoulli cumulant at unit dispersion is $X^\top\big(y - \sigma(\eta(\beta))\big)$.
