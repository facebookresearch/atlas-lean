# Potential-reduction l1 IPM: min-cost flow from m^(1+o(1)) approximate min-ratio cycles

Let an integral minimum-cost flow instance be given with optimal flow $\mathbf{f}^*$, let $\kappa \in (0, 1)$, and let $\mathbf{f}^{(0)}$ be feasible with $\Phi(\mathbf{f}^{(0)}) \le 200m\log(mU)$. Consider the method that, for $t = 0, 1, \ldots$, receives approximations $\widetilde{\mathbf{g}}, \widetilde{\boldsymbol{\ell}}$ satisfying $\|\mathbf{L}(\mathbf{f}^{(t)})^{-1}(\widetilde{\mathbf{g}} - \mathbf{g}(\mathbf{f}^{(t)}))\|_\infty \le \kappa/8$ and $\widetilde{\boldsymbol{\ell}} \approx_2 \boldsymbol{\ell}(\mathbf{f}^{(t)})$, receives any circulation $\mathbf{\Delta}$ with $\widetilde{\mathbf{g}}^{\top}\mathbf{\Delta}/\|\widetilde{\mathbf{L}}\mathbf{\Delta}\|_1 \le -\kappa$, and sets $\mathbf{f}^{(t+1)} = \mathbf{f}^{(t)} + \eta\mathbf{\Delta}$ with $\eta = \kappa^2/(50|\widetilde{\mathbf{g}}^{\top}\mathbf{\Delta}|)$. Then:

1. at every iteration the circulation $\mathbf{f}^* - \mathbf{f}^{(t)}$ witnesses minimum ratio at most $-\alpha/4$, so a $\Theta(\kappa/\alpha)$-approximate minimum-ratio cycle oracle supplies a valid $\mathbf{\Delta}$;
2. after $\widetilde{O}(m\kappa^{-2})$ iterations, $\mathbf{c}^{\top}\mathbf{f}^{(t)} \le F^* + (mU)^{-10}$.

With $\kappa = m^{-o(1)}$ the method uses $m^{1+o(1)}$ iterations, in contrast to the $\widetilde{O}(\sqrt{m})$ or $\widetilde{O}(\sqrt{n})$ iterations of path-following methods that solve a Laplacian system per iteration.

## Proof sketch

Item 1 is *The direction to an optimal flow is a good minimum-ratio witness*. By *One approximate minimum-ratio step decreases the IPM potential by a constant times kappa squared* each iteration lowers $\Phi$ by at least $\kappa^2/500$ while keeping the iterate strictly feasible. Starting from $\Phi \le 200m\log(mU)$, after $\widetilde{O}(m\kappa^{-2})$ iterations the potential is at most $-200m\log(mU)$, and *A very negative IPM potential certifies a near-optimal flow* converts this into the stated cost bound.

## Depends on

- [Integral minimum-cost flow instances with polynomially bounded data](integral-min-cost-flow-instance.md)
- [Potential function of the l1 interior point method for minimum-cost flow](l1-ipm-potential-function.md)
- [Lengths and gradients induced by the l1 IPM potential](ipm-lengths-and-gradients.md)
- [Undirected minimum-ratio cycle problem with gradients and lengths](undirected-min-ratio-cycle-problem.md)

## Proof depends on

- [One approximate minimum-ratio step decreases the IPM potential by a constant times kappa squared](one-step-potential-decrease.md)
- [A very negative IPM potential certifies a near-optimal flow](potential-certifies-near-optimal-flow.md)
- [The direction to an optimal flow is a good minimum-ratio witness](optimal-direction-min-ratio-witness.md)

## Sources

- Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, "Maximum Flow and Minimum-Cost Flow in Almost-Linear Time", FOCS (2022), arXiv:2203.00671.
- Samuel I. Daitch, Daniel A. Spielman, "Faster Approximate Lossy Generalized Flow via Interior Point Algorithms", STOC (2008), arXiv:0803.0988.
- Aleksander Madry, "Navigating Central Path with Electrical Flows: From Flows to Matchings, and Back", FOCS (2013), arXiv:1307.2205.
- Yin Tat Lee, Aaron Sidford, "Path Finding Methods for Linear Programming", FOCS (2014), arXiv:1312.6677.
