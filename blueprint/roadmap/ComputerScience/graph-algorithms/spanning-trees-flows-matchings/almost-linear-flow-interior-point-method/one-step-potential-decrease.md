# One approximate minimum-ratio step decreases the IPM potential by a constant times kappa squared

Let $\mathbf{f}$ lie in the domain of the potential with $\Phi(\mathbf{f}) \le 200m\log(mU)$, let $\kappa \in (0, 1)$, and let $\widetilde{\mathbf{g}} \in \mathbb{R}^E$ and $\widetilde{\boldsymbol{\ell}} \in \mathbb{R}^E_{>0}$ satisfy $\|\mathbf{L}(\mathbf{f})^{-1}(\widetilde{\mathbf{g}} - \mathbf{g}(\mathbf{f}))\|_\infty \le \kappa/8$ and $\widetilde{\boldsymbol{\ell}} \approx_2 \boldsymbol{\ell}(\mathbf{f})$, with $\widetilde{\mathbf{L}} = \mathrm{diag}(\widetilde{\boldsymbol{\ell}})$. Let $\mathbf{\Delta}$ be a circulation with $\widetilde{\mathbf{g}}^{\top}\mathbf{\Delta}/\|\widetilde{\mathbf{L}}\mathbf{\Delta}\|_1 \le -\kappa$, and set $\eta = \kappa^2/(50\,|\widetilde{\mathbf{g}}^{\top}\mathbf{\Delta}|)$ and $\mathbf{f}' = \mathbf{f} + \eta\mathbf{\Delta}$. Then for every edge $e$

$$
\eta|\mathbf{\Delta}_e| \le \frac{\kappa}{10}\min\{\mathbf{u}^+_e - \mathbf{f}_e,\ \mathbf{f}_e - \mathbf{u}^-_e\},
$$

so $\mathbf{f}'$ is feasible and strictly inside the box, and $\Phi(\mathbf{f}') \le \Phi(\mathbf{f}) - \kappa^2/500$.

## Proof sketch

First $\|\mathbf{L}(\mathbf{f})\eta\mathbf{\Delta}\|_1 \le 2\|\widetilde{\mathbf{L}}\eta\mathbf{\Delta}\|_1 \le (2\eta/\kappa)|\widetilde{\mathbf{g}}^{\top}\mathbf{\Delta}| \le \kappa/25$, and since $\boldsymbol{\ell}_e \ge (\mathbf{u}^+_e - \mathbf{f}_e)^{-1-\alpha}$ with residuals at most $2U$ and $\alpha = 1/(1000\log(mU))$, each coordinate moves by at most $\kappa/10$ of its residual capacity. A second-order Taylor bound for the barrier terms and for the logarithm on this small region shows that $\Phi(\mathbf{f}') - \Phi(\mathbf{f})$ is at most $\mathbf{g}(\mathbf{f})^{\top}\eta\mathbf{\Delta}$ plus $O(\|\mathbf{L}\eta\mathbf{\Delta}\|_1^2)$. Replacing $\mathbf{g}$ by $\widetilde{\mathbf{g}}$ costs $(\kappa/8)\|\mathbf{L}\eta\mathbf{\Delta}\|_1$, while $\widetilde{\mathbf{g}}^{\top}\eta\mathbf{\Delta} = -\kappa^2/50$; collecting terms gives a decrease of at least $\kappa^2/500$.

## Depends on

- [Lengths and gradients induced by the l1 IPM potential](ipm-lengths-and-gradients.md)
- [Potential function of the l1 interior point method for minimum-cost flow](l1-ipm-potential-function.md)

## Sources

- Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, "Maximum Flow and Minimum-Cost Flow in Almost-Linear Time", FOCS (2022), arXiv:2203.00671.
