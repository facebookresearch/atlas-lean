# Matrix mean-value step for the Cox score

For survival data with observed times $T_i$, event indicators $\delta_i$ and covariate vectors $x_i \in \mathbb{R}^p$, let $U(\beta)$ be the Cox score vector and $I(\beta)$ the observed information matrix. If $c \ge 0$ and $I(b')$ is entrywise within $c$ of a matrix $A$ for $\|b' - \beta_0\|_\infty \le \varepsilon$, then $\|U(b) - U(\beta_0) + A(b - \beta_0)\|_\infty \le pc\|b - \beta_0\|_\infty$ on that ball.
