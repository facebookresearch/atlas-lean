# Poisson regression Hessian

For an $n \times p$ design $X$, offset $o$, responses $y \in \mathbb{R}^n$ and $\eta(\beta) = X\beta + o$, let $K(\beta) = \sum_i\big(y_i\eta_i(\beta) - e^{\eta_i(\beta)}\big)$ be the Poisson log-linear likelihood kernel. Then the canonical-link Hessian of the Poisson cumulant at unit dispersion is $-X^\top WX$ with $W = \operatorname{diag}(e^{\eta_i(\beta)})$.
