# Hidden stable flow chasing property of a dynamic min-ratio cycle instance

A dynamic min-ratio cycle instance is a dynamic graph $G^{(t)}$ undergoing batches $U^{(1)}, U^{(2)}, \ldots$ of edge insertions, edge deletions and vertex splits, with gradients $\mathbf{g}^{(t)}$ and lengths $\boldsymbol{\ell}^{(t)} > 0$. Vectors $\mathbf{c}, \mathbf{w}$ form a valid pair for lengths $\boldsymbol{\ell}$ if $\mathbf{c}$ is a circulation and $|\boldsymbol{\ell}_e\mathbf{c}_e| \le \mathbf{w}_e$ for all $e$. For $\alpha > 0$ the instance satisfies the hidden stable $\alpha$-flow chasing property if there exist (unknown to the algorithm) circulations $\mathbf{c}^{(t)}$ and bounds $\mathbf{w}^{(t)}$ such that at every stage $t$:

1. $\mathbf{B}^{\top}_{G^{(t)}}\mathbf{c}^{(t)} = \mathbf{0}$ and $(\mathbf{c}^{(t)}, \mathbf{w}^{(t)})$ is a valid pair for $\boldsymbol{\ell}^{(t)}$;
2. $\langle\mathbf{g}^{(t)}, \mathbf{c}^{(t)}\rangle/\|\mathbf{w}^{(t)}\|_1 \le -\alpha$;
3. for every edge $e$ of $G^{(t)}$ and stage $t' \le t$ such that $e$ was not explicitly inserted after stage $t'$, $\mathbf{w}^{(t)}_e \le 2\mathbf{w}^{(t')}_e$;
4. $\log\mathbf{w}^{(t)}_e$ and $\log\boldsymbol{\ell}^{(t)}_e$ lie in $[-\log^{O(1)} m, \log^{O(1)} m]$.

In the l1 IPM one takes $\mathbf{c}^{(t)} = \mathbf{f}^* - \mathbf{f}^{(t)}$ and $\mathbf{w}^{(t)}_e = O(1) + |\boldsymbol{\ell}(\mathbf{f}^{(t)})_e\, \mathbf{c}^{(t)}_e|$, with $\alpha = 1/\Theta(\log m)$.

## Depends on

- [Undirected minimum-ratio cycle problem with gradients and lengths](../almost-linear-flow-interior-point-method/undirected-min-ratio-cycle-problem.md)
- [Dynamic graph problems](../../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/dynamic-graph-problems.md)

## Sources

- Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, "Maximum Flow and Minimum-Cost Flow in Almost-Linear Time", FOCS (2022), arXiv:2203.00671.
- Jan van den Brand, Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, Aaron Sidford, "A Deterministic Almost-Linear Time Algorithm for Minimum-Cost Flow", FOCS (2023), arXiv:2309.16629.
