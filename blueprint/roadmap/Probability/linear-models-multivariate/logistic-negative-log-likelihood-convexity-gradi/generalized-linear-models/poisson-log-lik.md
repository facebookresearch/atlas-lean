# Poisson log-linear log-likelihood of counts

For a design $X$, offset $o$ and counts $y \in \mathbb{N}^n$, the canonical Poisson log-likelihood is $\sum_i\big(y_i\eta_i(\beta) - e^{\eta_i(\beta)} - \log y_i!\big)$, the log-probability of $y$ under independent $Y_i \sim \mathrm{Poisson}(e^{\eta_i(\beta)})$, $\eta(\beta) = X\beta + o$.
