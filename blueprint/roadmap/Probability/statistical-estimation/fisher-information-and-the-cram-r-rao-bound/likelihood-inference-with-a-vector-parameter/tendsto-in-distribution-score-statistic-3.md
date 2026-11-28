# Score test, vector parameter

Let $E$ be a finite-dimensional real inner product space, $\nu$ a measure, $p_\theta$ ($\theta \in E$) densities with respect to $\nu$, $P_\theta = p_\theta\,\nu$, $s_\theta = \nabla_\theta\log p_\theta$ the score and $I(\theta)$ the Fisher information operator. Let $X_0, X_1, \dots$ be mutually independent observations with law $P_{\theta_0}$. Assume $s_{\theta_0}$ is measurable with $\int\|s_{\theta_0}\|^2dP_{\theta_0} < \infty$ and $\int s_{\theta_0}\,dP_{\theta_0} = 0$. Assume $I(\theta_0)$ is positive definite and $d = \dim E \ge 1$. With $S_n = n^{-1/2}\sum_{i<n}s_{\theta_0}(X_i)$, the score statistic $\langle I(\theta_0)^{-1}S_n, S_n\rangle$ converges in distribution to the chi-square law with $d$ degrees of freedom.

## Sources

- Rao (1948); van der Vaart (1998), ch. 16.
