# Quadratic expansion of the log-likelihood ratio for a vector parameter

Let $E$ be a finite-dimensional real inner product space of parameters, $\nu$ a measure on an observation space, $p_\theta$ a density with respect to $\nu$ for each $\theta \in E$, $P_\theta$ the law with density $p_\theta$, $s_\theta(x) = \nabla_\theta\log p_\theta(x)$ the score, $\dot s_\theta(x)$ its derivative in $\theta$ (an operator on $E$), and $I(\theta) = \int s_\theta s_\theta^\top\,dP_\theta$ the Fisher information operator. Let $X_0, X_1, \dots$ be mutually independent observations on a probability space, each with law $P_{\theta_0}$. Assume that for some $\delta > 0$ the score is differentiable in $\theta$ on the ball $B(\theta_0, \delta)$ for every $x$, with $\|\dot s_\theta(x) - \dot s_{\theta_0}(x)\| \le M(x)\|\theta - \theta_0\|$ there for a measurable $P_{\theta_0}$-integrable $M$. Assume that $\theta \mapsto \log p_\theta(x)$ is differentiable on $B(\theta_0, \delta)$ for every $x$. Assume $s_{\theta_0}$ is measurable with $\int\|s_{\theta_0}\|^2dP_{\theta_0} < \infty$ and $\int s_{\theta_0}\,dP_{\theta_0} = 0$. Assume $\dot s_{\theta_0}$ is strongly measurable and integrable with $\int\dot s_{\theta_0}\,dP_{\theta_0} = -I(\theta_0)$ (the information identity). Assume $I(\theta_0)$ is invertible. Let $\hat\theta_n$ be almost everywhere measurable estimators with $\hat\theta_n \to \theta_0$ in probability that solve the likelihood equation $\sum_{i<n}s_{\hat\theta_n}(X_i) = 0$ with probability tending to $1$. With $\ell_n(\theta) = \sum_{i<n}\log p_\theta(X_i)$,

$$2\big(\ell_n(\hat\theta_n) - \ell_n(\theta_0)\big) - n\,\langle I(\theta_0)(\hat\theta_n - \theta_0), \hat\theta_n - \theta_0\rangle \to 0$$

in probability.

## Sources

- the second-order expansion of Wilks (1938); van der Vaart (1998), Theorem 16.7.
