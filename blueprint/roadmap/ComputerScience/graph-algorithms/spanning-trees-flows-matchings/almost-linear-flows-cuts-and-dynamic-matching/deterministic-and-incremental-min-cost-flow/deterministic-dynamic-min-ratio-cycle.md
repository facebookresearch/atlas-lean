# Deterministic dynamic min-ratio cycle data structure with hidden stability

There is a deterministic data structure that $\kappa$-approximately solves the dynamic min-ratio cycle problem with hidden stability (see *Approximate dynamic min-ratio cycle problem with hidden stability*) for

$$
\kappa = \exp\bigl(-O(\log^{17/18} m\cdot\log\log m)\bigr).
$$

Over $\tau$ batches $U^{(1)}, \ldots, U^{(\tau)}$ it runs in total time $m^{o(1)}(m + \sum_{t \le \tau}|U^{(t)}|)$. It maintains a spanning tree $T \subseteq G^{(t)}$, returns each cycle as $m^{o(1)}$ paths of $T$ given by endpoints together with $m^{o(1)}$ explicit off-tree edges, supports $\mathrm{Update}$ and $\mathrm{Query}$ in amortized $m^{o(1)}$ time, and runs $\mathrm{Detect}$ in time $m^{o(1)}|S^{(t)}|$ where $S^{(t)}$ is its output.

## Proof sketch

Maintain one shifted tree chain with $d = O(\log^{1/18} m)$ levels, using the deterministic dynamic low-stretch forests and the deterministic spanner *Deterministic dynamic spanners with low-recourse short embeddings under deletions and vertex splits*. If the best fundamental spanner or tree cycle has ratio worse than $\kappa\alpha$, then by *Hidden witnesses pass to core graphs and sparsified core graphs with bounded loss* either the hidden witness width dropped by a factor $2(d+1)$ relative to the representative times, or the stretch of the selected forest at some level exceeds $\widetilde{O}(1)$; by *Multiplicative weights give k low-stretch forests that are good on average for every edge* some forest at that level is good, so cyclic shifts find it. These events form an instance of the shift-and-rebuild game, and the player strategy that shifts the lowest failing level guarantees $s_i \le \sum_{i' \le i}r_{i'}(10\Psi k)^{i+1-i'}$, which bounds the total cost of shifts and rebuilds by $m^{o(1)}$ per update; link-cut trees maintain the flow.

## Depends on

- [Approximate dynamic min-ratio cycle problem with hidden stability](../dynamic-min-ratio-cycle-data-structures/dynamic-min-ratio-cycle-hidden-stability.md)

## Proof depends on

- [Hidden witnesses pass to core graphs and sparsified core graphs with bounded loss](../dynamic-min-ratio-cycle-data-structures/witness-circulations-pass-to-core-graphs.md)
- [Multiplicative weights give k low-stretch forests that are good on average for every edge](../dynamic-min-ratio-cycle-data-structures/mwu-low-stretch-forest-family.md)
- [Deterministic dynamic spanners with low-recourse short embeddings under deletions and vertex splits](../dynamic-min-ratio-cycle-data-structures/deterministic-dynamic-spanner-embedding.md)
- [Dynamic low-stretch forests with stable stretch overestimates](../dynamic-min-ratio-cycle-data-structures/dynamic-low-stretch-forest.md)
- [Link-cut trees take logarithmic amortized time](../../../../data-structures/disjoint-sets-and-dynamic-trees/link-cut-tree/link-cut-trees-take-logarithmic-amortized-time.md)
- [The shift-and-rebuild game for deterministic tree chains](shift-and-rebuild-game.md)
- [Tree chains with shifts and rebuilds over recursive sparsified core graphs](../dynamic-min-ratio-cycle-data-structures/shifted-tree-chain.md)

## Sources

- Jan van den Brand, Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, Aaron Sidford, "A Deterministic Almost-Linear Time Algorithm for Minimum-Cost Flow", FOCS (2023), arXiv:2309.16629.
