# Consistency of the observed information at a consistent estimator

Let $E$ be a finite-dimensional real inner product space of parameters, $\nu$ a measure on an observation space, $p_\theta$ a density with respect to $\nu$ for each $\theta \in E$, $P_\theta$ the law with density $p_\theta$, $s_\theta(x) = \nabla_\theta\log p_\theta(x)$ the score, $\dot s_\theta(x)$ its derivative in $\theta$ (an operator on $E$), and $I(\theta) = \int s_\theta s_\theta^\top\,dP_\theta$ the Fisher information operator. Let $X_0, X_1, \dots$ be mutually independent observations on a probability space, each with law $P_{\theta_0}$. Assume $\dot s_{\theta_0}$ is strongly measurable and integrable with $\int\dot s_{\theta_0}\,dP_{\theta_0} = -I(\theta_0)$ (the information identity). Write $\hat J_n(\theta) = -\frac1n\sum_{i<n}\dot s_\theta(X_i)$ for the observed information. Assume moreover that for some $\delta > 0$, $\|\dot s_\theta(x) - \dot s_{\theta_0}(x)\| \le M(x)\|\theta - \theta_0\|$ for $\theta \in B(\theta_0, \delta)$ with a measurable $P_{\theta_0}$-integrable $M$. Then for all almost everywhere measurable estimators $\hat\theta_n \to \theta_0$ in probability, $\hat J_n(\hat\theta_n) \to I(\theta_0)$ in probability.

## Sources

- van der Vaart (1998), §5.6 (consistency of the plug-in observed information).
