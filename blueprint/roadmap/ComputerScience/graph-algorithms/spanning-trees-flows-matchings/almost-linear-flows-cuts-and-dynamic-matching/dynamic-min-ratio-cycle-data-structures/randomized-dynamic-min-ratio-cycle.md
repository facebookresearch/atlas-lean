# Randomized dynamic min-ratio cycle data structure under hidden stable flow chasing

There is a randomized data structure that, on a dynamic graph $G^{(t)}$ with at most $m$ edges whose updates, gradients and lengths satisfy the hidden stable $\alpha$-flow chasing property, maintains $s = O(\log n)^d$ spanning trees $T_1, \ldots, T_s$ for $d = O(\log^{1/8} m)$ and after each update returns, for some $i \in [s]$, a circulation $\mathbf{\Delta}$ represented by $m^{o(1)}$ paths of $T_i$ (given by endpoints and the tree index) and $m^{o(1)}$ explicit off-tree edges such that

$$
\frac{\langle\mathbf{g}^{(t)}, \mathbf{\Delta}\rangle}{\|\mathbf{L}^{(t)}\mathbf{\Delta}\|_1} \le -\kappa\alpha, \qquad \kappa = m^{-o(1)}.
$$

It supports updating gradients and lengths of the edges returned by the flow-maintenance routine in amortized $m^{o(1)}$ time, and over $m^{1+o(1)}$ updates it runs in $m^{1+o(1)}$ total time, succeeding with high probability.

## Proof sketch

Maintain $\widetilde{O}(1)^d$ branching tree chains whose levels are dynamic low-stretch forests and dynamic sparsified core graphs, so each chain defines a spanning tree and the fundamental cycles of the spanner at every level. By *Hidden witnesses pass to core graphs and sparsified core graphs with bounded loss* the hidden witness descends the chain with width multiplied by $\widetilde{O}(k)$ per level, and by *Multiplicative weights give k low-stretch forests that are good on average for every edge* and *Low stretch preserves a minimum-ratio cycle among fundamental tree cycles* at least one sampled branch preserves a cycle of ratio within $\exp(-O(d\log\log m))\cdot m^{-o(1)}$ of the witness. When a chain fails to output a good cycle, hidden stability implies that either its stretch on the witness grew or the witness width shrank, so the corresponding levels are rebuilt; a rebuilding game charges these rebuilds so that the total cost is $m^{1+o(1)}$, and link-cut trees apply the flow updates along tree paths.

## Depends on

- [Approximate dynamic min-ratio cycle problem with hidden stability](dynamic-min-ratio-cycle-hidden-stability.md)
- [Hidden stable flow chasing property of a dynamic min-ratio cycle instance](hidden-stable-flow-chasing.md)

## Proof depends on

- [Hidden witnesses pass to core graphs and sparsified core graphs with bounded loss](witness-circulations-pass-to-core-graphs.md)
- [Multiplicative weights give k low-stretch forests that are good on average for every edge](mwu-low-stretch-forest-family.md)
- [Low stretch preserves a minimum-ratio cycle among fundamental tree cycles](tree-cycles-approximate-min-ratio.md)
- [Deterministic dynamic spanners with low-recourse short embeddings under deletions and vertex splits](deterministic-dynamic-spanner-embedding.md)
- [Link-cut trees take logarithmic amortized time](../../../../data-structures/disjoint-sets-and-dynamic-trees/link-cut-tree/link-cut-trees-take-logarithmic-amortized-time.md)
- [Tree chains with shifts and rebuilds over recursive sparsified core graphs](shifted-tree-chain.md)

## Sources

- Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, "Maximum Flow and Minimum-Cost Flow in Almost-Linear Time", FOCS (2022), arXiv:2203.00671.
