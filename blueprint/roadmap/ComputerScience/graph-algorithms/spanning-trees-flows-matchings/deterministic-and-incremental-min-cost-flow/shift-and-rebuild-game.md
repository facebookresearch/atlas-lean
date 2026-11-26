# The shift-and-rebuild game for deterministic tree chains

Fix $d$ levels, $k$ branches per level and a range parameter $\Psi \ge 1$. The shift-and-rebuild game is played between a player and an adversary over rounds $t = 1, \ldots, T$. Each level $i$ has a shift index $\mathrm{shift}_i \in \{0, \ldots, k-1\}$, a representative time $\overline{\mathrm{repT}}_i$, and hidden nonnegative stretch values $\overline{\mathrm{str}}_{i,j}$ for its branches $j$ that are valid, meaning some branch has value $\widetilde{O}(1)$. In each round the adversary chooses a hidden weight $W^{(t)}$ with $\log_2 W^{(t)} \in (-\Psi, \Psi)$, may announce a $\mathrm{rebuild}(i)$ step, which resets $\mathrm{shift}_{i'} = 0$ and $\overline{\mathrm{repT}}_{i'} = t$ and draws new valid hidden stretches for all $i' \ge i$, and may then repeatedly declare the round unfinished while the current configuration has a level whose selected branch has large stretch or whose representative weight is much larger than $W^{(t)}$; each time, the player answers with a $\mathrm{shift}(i)$ step, which advances $\mathrm{shift}_i$ cyclically and resets the levels above $i$. Let $r_i$ and $s_i$ count the rebuilds and shifts at level $i$.

## Depends on

- [Tree chains with shifts and rebuilds over recursive sparsified core graphs](../dynamic-min-ratio-cycle-data-structures/shifted-tree-chain.md)

## Sources

- Jan van den Brand, Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, Aaron Sidford, "A Deterministic Almost-Linear Time Algorithm for Minimum-Cost Flow", FOCS (2023), arXiv:2309.16629.
