# The profile log-likelihood of a SNP effect is an exact quadratic

Let $(K, \sigma_g^2, \sigma_e^2)$ be [variance components](model.md) on $n$ individuals, let $X$ be a real $n \times p$ matrix of full column rank with [residual-forming matrix](proj.md) $P$, and let $x, y \in \mathbb{R}^n$. Then for every $\gamma \in \mathbb{R}$ the [profile log-likelihood](profile-log-lik.md) satisfies

$$\ell_{\mathrm{prof}}(\gamma) = \ell_{\mathrm{prof}}(0) + \gamma\, x^\top P y - \frac{\gamma^2}{2}\, x^\top P x.$$

So its score at $\gamma = 0$ is $x^\top P y$ and its information is $x^\top P x$.
