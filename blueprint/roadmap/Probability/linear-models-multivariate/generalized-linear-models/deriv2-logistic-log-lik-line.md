# Second derivative of the logistic log-likelihood along a line

For an $n \times p$ design $X$, offset $o$, responses $y \in \mathbb{R}^n$ and $\eta(\beta) = X\beta + o$, let $\ell(\beta) = \sum_i\big(y_i\eta_i(\beta) - \log(1 + e^{\eta_i(\beta)})\big)$ be the logistic regression log-likelihood and $\sigma(t) = 1/(1 + e^{-t})$. Then for all $\beta$ and $u$, the second derivative of $t \mapsto \ell(\beta + tu)$ at $0$ is $-\sum_i\sigma(\eta_i)(1 - \sigma(\eta_i))\,(Xu)_i^2$.
