# Directional pleiotropy biases the IVW estimator

Let $\iota$ be a finite set of SNPs, let $\sigma_j > 0$ for every $j$, let $\gamma \in \mathbb{R}^\iota$ with $\gamma_j \ne 0$ for some $j$, let $\alpha \in \mathbb{R}^\iota$ and $\beta \in \mathbb{R}$, and put $\Gamma_j = \alpha_j + \beta \gamma_j$. Then the [IVW estimator](ivw.md) of $(\gamma, \Gamma, \sigma)$ is

$$\hat\beta_{\mathrm{IVW}} = \beta + \frac{\sum_j \gamma_j \alpha_j / \sigma_j^2}{\sum_j \gamma_j^2 / \sigma_j^2}.$$

For example, a common pleiotropic term $\alpha_j = \alpha \ne 0$ biases the estimator whenever $\sum_j \gamma_j / \sigma_j^2 \ne 0$, although a constant $\alpha$ satisfies InSIDE.
