# Gradient of the Poisson log-linear kernel

For an $n \times p$ design $X$, offset $o$, responses $y \in \mathbb{R}^n$ and $\eta(\beta) = X\beta + o$, let $K(\beta) = \sum_i\big(y_i\eta_i(\beta) - e^{\eta_i(\beta)}\big)$ be the Poisson log-linear likelihood kernel. Then for every $\beta$, the Euclidean gradient of $K$ is $X^\top(y - e^{\eta(\beta)})$.
