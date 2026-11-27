# Approximate dynamic min-ratio cycle problem with hidden stability

Let a dynamic instance satisfy the hidden stable $\alpha$-flow chasing property (see *Hidden stable flow chasing property of a dynamic min-ratio cycle instance*) and let $\kappa \in (0, 1]$. The $\kappa$-approximate dynamic min-ratio cycle problem with hidden stability asks for a data structure that maintains a flow $\mathbf{f} \in \mathbb{R}^E$, initially $\mathbf{0}$, and supports:

1. $\mathrm{Update}(U^{(t)}, \mathbf{g}^{(t)}, \boldsymbol{\ell}^{(t)}, \eta)$: apply the batch, change the gradients and lengths of the listed edges, find a circulation $\mathbf{\Delta}^{(t)}$ with $\langle\mathbf{g}^{(t)}, \mathbf{\Delta}^{(t)}\rangle/\|\mathbf{L}^{(t)}\mathbf{\Delta}^{(t)}\|_1 \le -\kappa\alpha$, and set $\mathbf{f} \leftarrow \mathbf{f} - \beta\mathbf{\Delta}^{(t)}$ with $\beta = \eta/\langle\mathbf{g}^{(t)}, \mathbf{\Delta}^{(t)}\rangle$;
2. $\mathrm{Query}(e)$: return $\mathbf{f}_e$;
3. $\mathrm{Detect}()$: for a fixed $\varepsilon$, return the edges $e$ with $\boldsymbol{\ell}_e\sum_{t' = \mathrm{last}_e + 1}^{t}|\mathbf{\Delta}^{(t')}_e| \ge \varepsilon$, where $\mathrm{last}_e$ is the last stage at which $e$ was returned.

The approximation is measured against the hidden witness, not against the true optimum, and the adversary generating updates is restricted by the hidden stability property rather than fully adaptive.

## Depends on

- [Hidden stable flow chasing property of a dynamic min-ratio cycle instance](hidden-stable-flow-chasing.md)
- [Amortized cost of an operation](../../../../data-structures/amortized-analysis/amortized-cost.md)

## Sources

- Jan van den Brand, Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, Aaron Sidford, "A Deterministic Almost-Linear Time Algorithm for Minimum-Cost Flow", FOCS (2023), arXiv:2309.16629.
- Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, "Maximum Flow and Minimum-Cost Flow in Almost-Linear Time", FOCS (2022), arXiv:2203.00671.
