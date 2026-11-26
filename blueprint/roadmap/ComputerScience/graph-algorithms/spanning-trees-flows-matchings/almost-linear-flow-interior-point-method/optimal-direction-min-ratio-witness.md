# The direction to an optimal flow is a good minimum-ratio witness

Let $\mathbf{f}$ lie in the domain of the potential with $\Phi(\mathbf{f}) \le 200m\log(mU)$, let $\mathbf{f}^*$ be a minimum-cost flow, and let $\kappa \in (0, 1)$. Let $\widetilde{\mathbf{g}} \in \mathbb{R}^E$ and $\widetilde{\boldsymbol{\ell}} \in \mathbb{R}^E_{>0}$ satisfy $\|\mathbf{L}(\mathbf{f})^{-1}(\widetilde{\mathbf{g}} - \mathbf{g}(\mathbf{f}))\|_\infty \le \kappa/8$ and $\widetilde{\boldsymbol{\ell}} \approx_2 \boldsymbol{\ell}(\mathbf{f})$, with $\widetilde{\mathbf{L}} = \mathrm{diag}(\widetilde{\boldsymbol{\ell}})$. Then the circulation $\mathbf{f}^* - \mathbf{f}$ satisfies

$$
\frac{\widetilde{\mathbf{g}}^{\top}(\mathbf{f}^* - \mathbf{f})}{100m + \|\widetilde{\mathbf{L}}(\mathbf{f}^* - \mathbf{f})\|_1} \le -\frac{\alpha}{4}.
$$

In particular the optimum of the minimum-ratio cycle problem for $(\widetilde{\mathbf{g}}, \widetilde{\boldsymbol{\ell}})$ is at most $-\alpha/4$, so any $m^{-o(1)}$-approximate solution has ratio at most $-m^{-o(1)}$.

## Proof sketch

The cost part of the gradient contributes exactly $20m\,\mathbf{c}^{\top}(\mathbf{f}^* - \mathbf{f})/(\mathbf{c}^{\top}\mathbf{f} - F^*) = -20m$. For the barrier part, a coordinate moving toward a capacity moves by at most the residual capacity, so its positive contribution is bounded by $\alpha$ times a power-$\alpha$ barrier value, which the bound $\Phi(\mathbf{f}) \le 200m\log(mU)$ keeps at $O(m)$ in total; a coordinate moving away from the nearer capacity contributes about $-\alpha\boldsymbol{\ell}_e|\mathbf{f}^*_e - \mathbf{f}_e|/2$. Summing, the exact gradient gives at most $-(\alpha/2)(100m + \|\mathbf{L}(\mathbf{f}^*-\mathbf{f})\|_1)$, and the $\kappa/8$ gradient error and factor-$2$ length error cost at most half of this.

## Depends on

- [Lengths and gradients induced by the l1 IPM potential](ipm-lengths-and-gradients.md)
- [Undirected minimum-ratio cycle problem with gradients and lengths](undirected-min-ratio-cycle-problem.md)
- [Potential function of the l1 interior point method for minimum-cost flow](l1-ipm-potential-function.md)

## Sources

- Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, "Maximum Flow and Minimum-Cost Flow in Almost-Linear Time", FOCS (2022), arXiv:2203.00671.
