# Second derivative of the Poisson kernel along a line

For an $n \times p$ design $X$, offset $o$, responses $y \in \mathbb{R}^n$ and $\eta(\beta) = X\beta + o$, let $K(\beta) = \sum_i\big(y_i\eta_i(\beta) - e^{\eta_i(\beta)}\big)$ be the Poisson log-linear likelihood kernel. Then for all $\beta$ and $u$, the second derivative of $t \mapsto K(\beta + tu)$ at $0$ is $-\sum_ie^{\eta_i(\beta)}(Xu)_i^2$.
