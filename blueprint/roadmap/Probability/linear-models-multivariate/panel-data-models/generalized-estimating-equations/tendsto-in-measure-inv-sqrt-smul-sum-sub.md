# Plugging in a root-n consistent nuisance estimate does not change the score

Let $U_i(\beta, \theta)$ be cluster scores at regression parameter $\beta$ and nuisance parameter $\theta$ (working correlation and scale), and $\hat\theta_n$ a random nuisance estimate. Assume the $U_i(\beta_0, \cdot)$ are differentiable on $B(\theta_0, \delta)$ for some $\delta > 0$ with derivatives $D_\theta U_i(\theta)$, $\sup_{\theta \in B(\theta_0, \delta)}\|n^{-1}\sum_{i<n}D_\theta U_i(\theta)\| \to 0$ in probability, and $\sqrt n(\hat\theta_n - \theta_0)$ is bounded in probability. Then $n^{-1/2}\sum_{i<n}\big(U_i(\beta_0, \hat\theta_n) - U_i(\beta_0, \theta_0)\big) \to 0$ in probability.

## Sources

- K.-Y. Liang and S. L. Zeger, "Longitudinal data analysis using generalized linear models", *Biometrika* 73 (1986), 13–22.
