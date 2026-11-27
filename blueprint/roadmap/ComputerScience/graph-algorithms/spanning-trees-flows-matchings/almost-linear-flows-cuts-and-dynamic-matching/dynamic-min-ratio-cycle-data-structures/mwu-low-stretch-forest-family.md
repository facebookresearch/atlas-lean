# Multiplicative weights give k low-stretch forests that are good on average for every edge

There is a deterministic algorithm that, given an $m$-edge graph $G$ with lengths $\boldsymbol{\ell}$ and an integer $k \ge 1$, computes in $\widetilde{O}(mk)$ time $k$ dynamic low-stretch forests (see *Dynamic low-stretch forests with stable stretch overestimates*) $(T_j, F_j, \widetilde{\mathrm{str}}^j)_{j=0}^{k-1}$ with fixed stretch overestimates such that for every edge $e$

$$
\frac{1}{k}\sum_{j=0}^{k-1}\widetilde{\mathrm{str}}^j_e \le O(\log^7 n).
$$

Consequently, for any fixed circulation $\mathbf{c}$ there is an index $j$ with $\sum_e\widetilde{\mathrm{str}}^j_e\boldsymbol{\ell}_e|\mathbf{c}_e| \le O(\log^7 n)\|\mathbf{L}\mathbf{c}\|_1$.

## Proof sketch

Run multiplicative weights over edges: start with $\mathbf{v} = \mathbf{1}$, build a forest by *Dynamic low-stretch forests with stable stretch overestimates* for the current weights, and multiply each $\mathbf{v}_e$ by $\exp(\Theta(\widetilde{\mathrm{str}}_e/(k\log^6 n)))$. Item 3 of that lemma bounds the weighted average stretch of each forest by $O(\log^4 n)$, and the standard regret analysis converts this into a uniform per-edge bound for the average over the $k$ rounds. The consequence follows by averaging $\sum_e\widetilde{\mathrm{str}}^j_e\boldsymbol{\ell}_e|\mathbf{c}_e|$ over $j$.

## Depends on

- [Stretch of an edge with respect to a rooted spanning forest](rooted-forest-edge-stretch.md)
- [Dynamic low-stretch forests with stable stretch overestimates](dynamic-low-stretch-forest.md)

## Sources

- Jan van den Brand, Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, Aaron Sidford, "A Deterministic Almost-Linear Time Algorithm for Minimum-Cost Flow", FOCS (2023), arXiv:2309.16629.
- Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, "Maximum Flow and Minimum-Cost Flow in Almost-Linear Time", FOCS (2022), arXiv:2203.00671.
