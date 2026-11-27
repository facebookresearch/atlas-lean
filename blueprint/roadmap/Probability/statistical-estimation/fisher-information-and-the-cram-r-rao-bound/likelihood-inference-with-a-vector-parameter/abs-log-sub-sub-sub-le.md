# Second-order expansion of the log-likelihood

Suppose that on $B(\theta_0, \delta)$ the log-density $\theta \mapsto \log p_\theta(x)$ is differentiable, its gradient $s_\theta(x)$ is differentiable, and $\|\dot s_\theta(x) - \dot s_{\theta_0}(x)\| \le C\|\theta - \theta_0\|$. Then for $\theta$ in the ball

$$\Big|\log p_\theta(x) - \log p_{\theta_0}(x) - \langle s_{\theta_0}(x), \theta - \theta_0\rangle - \tfrac12\langle\dot s_{\theta_0}(x)(\theta - \theta_0), \theta - \theta_0\rangle\Big| \le C\|\theta - \theta_0\|^3.$$
