# Gaussian rate-distortion function vanishes above the variance

Let $\sigma^2 \ge 0$ and $D \in \mathbb{R}$. The feasible set $\mathcal{F}(\sigma^2, D)$ consists of the probability measures $\mu$ on $\mathbb{R}^2$ with $D \ge 0$, first marginal $\mathcal{N}(0, \sigma^2)$, and $\int (x - \hat x)^2 \, d\mu(x, \hat x) \le D$ (a lower integral in $[0, \infty]$). The mutual information of $\mu$ in bits is $I(\mu) = D_{\mathrm{KL}}(\mu \,\|\, \mu_1 \otimes \mu_2) / \log 2 \in [0, \infty]$, where $\mu_1, \mu_2$ are the marginals, and the rate-distortion function is $R(D) = \inf_{\mu \in \mathcal{F}(\sigma^2, D)} I(\mu) \in [0, \infty]$.

If $\sigma^2 \le D$, then $R(D) = 0$.

In particular $R(\sigma^2) = 0$: the constant reconstruction $\hat{X} = 0$ is feasible at level $\sigma^2$ and carries zero mutual information. For the degenerate source $\mathcal{N}(0, 0) = \delta_0$ this gives $R(0) = 0$, so the hypothesis $\sigma^2 > 0$ for $R(0) = \infty$ cannot be dropped.
