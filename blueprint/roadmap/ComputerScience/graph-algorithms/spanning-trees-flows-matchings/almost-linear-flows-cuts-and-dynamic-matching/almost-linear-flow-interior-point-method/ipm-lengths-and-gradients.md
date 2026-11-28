# Lengths and gradients induced by the l1 IPM potential

For a flow $\mathbf{f}$ in the domain of the potential $\Phi$ (see *Potential function of the l1 interior point method for minimum-cost flow*) define the length vector $\boldsymbol{\ell}(\mathbf{f}) \in \mathbb{R}^E_{>0}$ and the gradient vector $\mathbf{g}(\mathbf{f}) = \nabla \Phi(\mathbf{f}) \in \mathbb{R}^E$ by

$$
\boldsymbol{\ell}(\mathbf{f})_e = (\mathbf{u}^+_e - \mathbf{f}_e)^{-1-\alpha} + (\mathbf{f}_e - \mathbf{u}^-_e)^{-1-\alpha},
$$

$$
\mathbf{g}(\mathbf{f})_e = \frac{20m\, \mathbf{c}_e}{\mathbf{c}^{\top}\mathbf{f} - F^*} + \alpha (\mathbf{u}^+_e - \mathbf{f}_e)^{-1-\alpha} - \alpha (\mathbf{f}_e - \mathbf{u}^-_e)^{-1-\alpha},
$$

and write $\mathbf{L}(\mathbf{f}) = \mathrm{diag}(\boldsymbol{\ell}(\mathbf{f}))$. The length of an edge grows as the flow on it approaches either capacity, so the residual capacities $\mathbf{u}^+_e - \mathbf{f}_e$ and $\mathbf{f}_e - \mathbf{u}^-_e$ of the residual graph are encoded in $\boldsymbol{\ell}(\mathbf{f})$. For positive vectors $\mathbf{a}, \mathbf{b}$ we write $\mathbf{a} \approx_2 \mathbf{b}$ if $\mathbf{b}_e/2 \le \mathbf{a}_e \le 2\mathbf{b}_e$ for all $e$.

## Depends on

- [Potential function of the l1 interior point method for minimum-cost flow](l1-ipm-potential-function.md)
- [Residual graph](../../edmonds-karp-algorithm/residual-graph.md)

## Sources

- Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, "Maximum Flow and Minimum-Cost Flow in Almost-Linear Time", FOCS (2022), arXiv:2203.00671.
