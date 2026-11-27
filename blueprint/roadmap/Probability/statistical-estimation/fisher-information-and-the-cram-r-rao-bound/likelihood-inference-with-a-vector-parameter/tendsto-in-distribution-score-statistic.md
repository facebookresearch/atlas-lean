# Score test with an estimated information

Let $E$ be a finite-dimensional real inner product space of parameters, $\nu$ a measure on an observation space, $p_\theta$ a density with respect to $\nu$ for each $\theta \in E$, $P_\theta$ the law with density $p_\theta$, $s_\theta(x) = \nabla_\theta\log p_\theta(x)$ the score, $\dot s_\theta(x)$ its derivative in $\theta$ (an operator on $E$), and $I(\theta) = \int s_\theta s_\theta^\top\,dP_\theta$ the Fisher information operator. Let $X_0, X_1, \dots$ be mutually independent observations on a probability space, each with law $P_{\theta_0}$. Assume $s_{\theta_0}$ is measurable with $\int\|s_{\theta_0}\|^2dP_{\theta_0} < \infty$ and $\int s_{\theta_0}\,dP_{\theta_0} = 0$. Assume $I(\theta_0)$ is positive definite and $d = \dim E \ge 1$. Let $\hat I_n$ be almost everywhere measurable operator-valued estimators with $\hat I_n \to I(\theta_0)$ in probability, and $S_n = n^{-1/2}\sum_{i<n}s_{\theta_0}(X_i)$. Then $\langle\hat I_n^{-1}S_n, S_n\rangle$ (with the inverse taken as $0$ at singular $\hat I_n$) converges in distribution to the chi-square law with $d$ degrees of freedom.

## Sources

- Rao (1948); van der Vaart (1998), ch. 16.
