# Lazy maintenance of IPM lengths and gradients with few coordinate changes

Run the l1 IPM steps $\mathbf{f} \leftarrow \mathbf{f} + \eta\mathbf{\Delta}$, where $\mathbf{\Delta}$ is a circulation with $\widetilde{\mathbf{g}}^{\top}\mathbf{\Delta}/\|\widetilde{\mathbf{L}}\mathbf{\Delta}\|_1 \le -\kappa$ and $\eta = \kappa^2/(50|\widetilde{\mathbf{g}}^{\top}\mathbf{\Delta}|)$ for the current approximations $\widetilde{\mathbf{g}}, \widetilde{\boldsymbol{\ell}}$ maintained below and $\widetilde{\mathbf{L}} = \mathrm{diag}(\widetilde{\boldsymbol{\ell}})$, for $\tau = \widetilde{O}(m\kappa^{-2})$ iterations, producing flows $\mathbf{f}^{(0)}, \mathbf{f}^{(1)}, \ldots$ with steps $\mathbf{\Delta}^{(t)} = \mathbf{f}^{(t)} - \mathbf{f}^{(t-1)}$. Maintain $\widetilde{\mathbf{g}}$ and $\widetilde{\boldsymbol{\ell}}$ lazily: coordinate $e$ is recomputed exactly at iteration $t$ only when

$$
\boldsymbol{\ell}_e(\mathbf{f}^{(\mathrm{last}_e)}) \sum_{t' = \mathrm{last}_e + 1}^{t} |\mathbf{\Delta}^{(t')}_e| \ge \varepsilon
$$

for a threshold $\varepsilon = \Theta(\kappa)$, where $\mathrm{last}_e$ is its previous recomputation. Then at every iteration $t$ the approximations satisfy $\|\mathbf{L}(\mathbf{f}^{(t)})^{-1}(\widetilde{\mathbf{g}} - \mathbf{g}(\mathbf{f}^{(t)}))\|_\infty \le \kappa/8$ and $\widetilde{\boldsymbol{\ell}} \approx_2 \boldsymbol{\ell}(\mathbf{f}^{(t)})$, and the total number of coordinate recomputations over the run is $\widetilde{O}(m\kappa^{-2})$.

## Proof sketch

Between recomputations the $\boldsymbol{\ell}$-weighted movement of coordinate $e$ is below $\varepsilon$, so its residual capacities change by a factor $1 \pm O(\varepsilon)$; this keeps $\widetilde{\boldsymbol{\ell}} \approx_2 \boldsymbol{\ell}$ and keeps the barrier part of the gradient within $(\kappa/16)\boldsymbol{\ell}_e$, while the common cost factor $20m/(\mathbf{c}^{\top}\mathbf{f} - F^*)$ is a single scalar that is refreshed globally. Each step has $\|\mathbf{L}\mathbf{\Delta}^{(t)}\|_1 \le \kappa/25$, so the total weighted movement over $\tau$ steps is $O(\tau\kappa)$ and each recomputation consumes $\Omega(\kappa)$ of it; hence there are $O(\tau) = \widetilde{O}(m\kappa^{-2})$ recomputations.

## Depends on

- [Lengths and gradients induced by the l1 IPM potential](ipm-lengths-and-gradients.md)

## Proof depends on

- [One approximate minimum-ratio step decreases the IPM potential by a constant times kappa squared](one-step-potential-decrease.md)

## Sources

- Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, "Maximum Flow and Minimum-Cost Flow in Almost-Linear Time", FOCS (2022), arXiv:2203.00671.
- Jan van den Brand, Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, Aaron Sidford, "A Deterministic Almost-Linear Time Algorithm for Minimum-Cost Flow", FOCS (2023), arXiv:2309.16629.
