# Logistic regression log-likelihood

For a design $X$, offset $o$ and responses $y$, the canonical Bernoulli (logistic regression) log-likelihood is $\ell(\beta) = \sum_i\big(y_i\eta_i(\beta) - \log(1 + e^{\eta_i(\beta)})\big)$ with $\eta(\beta) = X\beta + o$; for $y_i \in \{0, 1\}$ each term is $\log P(Y_i = y_i)$ under success probability $\sigma(\eta_i)$.
