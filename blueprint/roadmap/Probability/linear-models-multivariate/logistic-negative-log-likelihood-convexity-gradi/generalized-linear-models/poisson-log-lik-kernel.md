# Poisson log-linear likelihood kernel

For a design $X$, offset $o$ and real responses $y$, the Poisson log-linear kernel is $K(\beta) = \sum_i\big(y_i\eta_i(\beta) - e^{\eta_i(\beta)}\big)$ with $\eta(\beta) = X\beta + o$; for counts it differs from the Poisson log-likelihood by the term $\sum_i\log y_i!$, free of $\beta$.
