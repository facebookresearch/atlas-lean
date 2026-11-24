# The score of a SNP effect

Let $(K, \sigma_g^2, \sigma_e^2)$ be [variance components](model.md) on $n$ individuals, let $X$ be a real $n \times p$ matrix of full column rank with [residual-forming matrix](proj.md) $P$, and let $x, y \in \mathbb{R}^n$. Then the [profile log-likelihood](profile-log-lik.md) $\ell_{\mathrm{prof}}$ is differentiable at $\gamma = 0$ with derivative

$$\ell_{\mathrm{prof}}'(0) = x^\top P y.$$
