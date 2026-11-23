# Consistency of the observed information

In the setting of [Rao's score test](tendsto-in-distribution-score-statistic.md) ($X_0, X_1, \dots$ independent with law $P_{\theta_0}$), assume only that $x \mapsto \partial_\theta s_\theta(x)|_{\theta_0}$ is measurable and $P_{\theta_0}$-integrable with $\mathbb{E}[\partial_\theta s_{\theta_0}(X_0)] = -I(\theta_0)$ (the information identity). Then the observed information converges in probability:

$$-\frac{1}{n} \sum_{i=0}^{n-1} \partial_\theta s_{\theta_0}(X_i) \to I(\theta_0).$$
