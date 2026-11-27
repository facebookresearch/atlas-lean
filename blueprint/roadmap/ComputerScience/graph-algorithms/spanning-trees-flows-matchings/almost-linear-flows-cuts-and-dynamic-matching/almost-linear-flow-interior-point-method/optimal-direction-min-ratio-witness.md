# The direction to an optimal flow is a good minimum-ratio witness

Let $\mathbf{f}$ lie in the domain of the potential with $\Phi(\mathbf{f}) \le 200m\log(mU)$ and $\mathbf{c}^{\top}\mathbf{f} - F^* \ge (mU)^{-10}$, and let $\mathbf{f}^*$ be a minimum-cost flow. Let $\widetilde{\mathbf{g}} \in \mathbb{R}^E$ and $\widetilde{\boldsymbol{\ell}} \in \mathbb{R}^E_{>0}$ satisfy $\|\mathbf{L}(\mathbf{f})^{-1}(\widetilde{\mathbf{g}} - \mathbf{g}(\mathbf{f}))\|_\infty \le \varepsilon$ for some $\varepsilon < \alpha/2$ and $\widetilde{\boldsymbol{\ell}} \approx_2 \boldsymbol{\ell}(\mathbf{f})$, with $\widetilde{\mathbf{L}} = \mathrm{diag}(\widetilde{\boldsymbol{\ell}})$. Then the circulation $\mathbf{f}^* - \mathbf{f}$ satisfies

$$
\frac{\widetilde{\mathbf{g}}^{\top}(\mathbf{f}^* - \mathbf{f})}{100m + \|\widetilde{\mathbf{L}}(\mathbf{f}^* - \mathbf{f})\|_1} \le -\frac{\alpha}{4}.
$$

In particular the optimum of the minimum-ratio cycle problem for $(\widetilde{\mathbf{g}}, \widetilde{\boldsymbol{\ell}})$ is at most $-\alpha/4$, so when $\log U \le m^{o(1)}$ any $m^{-o(1)}$-approximate solution has ratio at most $-m^{-o(1)}$.

## Proof sketch

The cost part of the gradient contributes exactly $20m\,\mathbf{c}^{\top}(\mathbf{f}^* - \mathbf{f})/(\mathbf{c}^{\top}\mathbf{f} - F^*) = -20m$. For the barrier part, since $\mathbf{u}^-_e - \mathbf{f}_e \le \mathbf{f}^*_e - \mathbf{f}_e \le \mathbf{u}^+_e - \mathbf{f}_e$, each edge contributes at most $-\alpha\boldsymbol{\ell}_e|\mathbf{f}^*_e - \mathbf{f}_e|$ plus twice $\alpha$ times its two barrier terms. The barrier sum equals $\Phi(\mathbf{f}) - 20m\log(\mathbf{c}^{\top}\mathbf{f} - F^*) \le 400m\log(mU)$ by the two hypotheses, so with $\alpha = 1/(1000\log(mU))$ the exact gradient gives $\mathbf{g}(\mathbf{f})^{\top}(\mathbf{f}^* - \mathbf{f}) \le -19m - \alpha\|\mathbf{L}(\mathbf{f})(\mathbf{f}^*-\mathbf{f})\|_1$. The gradient error costs at most $\varepsilon\|\mathbf{L}(\mathbf{f})(\mathbf{f}^*-\mathbf{f})\|_1 < (\alpha/2)\|\mathbf{L}(\mathbf{f})(\mathbf{f}^*-\mathbf{f})\|_1$, and $\widetilde{\boldsymbol{\ell}} \approx_2 \boldsymbol{\ell}(\mathbf{f})$ bounds the denominator by $100m + 2\|\mathbf{L}(\mathbf{f})(\mathbf{f}^*-\mathbf{f})\|_1$.

## Depends on

- [Lengths and gradients induced by the l1 IPM potential](ipm-lengths-and-gradients.md)
- [Undirected minimum-ratio cycle problem with gradients and lengths](undirected-min-ratio-cycle-problem.md)
- [Potential function of the l1 interior point method for minimum-cost flow](l1-ipm-potential-function.md)

## Sources

- Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, "Maximum Flow and Minimum-Cost Flow in Almost-Linear Time", FOCS (2022), arXiv:2203.00671.
