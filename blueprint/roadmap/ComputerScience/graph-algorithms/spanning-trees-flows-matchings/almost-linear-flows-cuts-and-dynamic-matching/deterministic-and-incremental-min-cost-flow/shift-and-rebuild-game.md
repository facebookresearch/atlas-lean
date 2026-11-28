# The shift-and-rebuild game for deterministic tree chains

Fix levels $0, \ldots, d$, $k$ branches per level and a range parameter $\Psi \ge 1$. The shift-and-rebuild game is played between a player and an adversary over rounds $t = 1, \ldots, T$. Each level $i$ has a shift index $\mathrm{shift}_i \in \{0, \ldots, k-1\}$, a representative round $\mathrm{repT}_i$, and hidden stretch values $\mathrm{str}_{i,j} \ge 0$ for its branches $j$, chosen by the adversary and always valid, meaning that some branch of the level has value $\widetilde{O}(1)$. Initially $\mathrm{shift}_i = 0$ and $\mathrm{repT}_i = 1$. Each round $t$ runs as follows.

1. The adversary chooses a hidden weight $W^{(t)} > 0$ with $\log_2 W^{(t)} \in (-\Psi, \Psi)$.
2. The adversary may take a step $\mathrm{rebuild}(i)$, announced to the player: for all $i' \ge i$ it sets $\mathrm{shift}_{i'} = 0$ and $\mathrm{repT}_{i'} = t$ and chooses new valid stretch values.
3. The adversary declares the round completing or continuing. It may declare it continuing only if $\sum_{i=0}^{d}W^{(\mathrm{repT}_i)} > 2(d+1)W^{(t)}$, or if some level $i$ has $\mathrm{str}_{i,\mathrm{shift}_i}$ larger than a fixed $\widetilde{\Omega}(1)$ threshold; the player learns the declaration but not which condition held.
4. The player does nothing or takes a step $\mathrm{shift}(i)$: for all $i' > i$ it sets $\mathrm{shift}_{i'} = 0$ and $\mathrm{repT}_{i'} = t$ and the adversary chooses new valid stretch values; then $\mathrm{shift}_i$ advances by one modulo $k$, and if it returns to $0$, $\mathrm{repT}_i$ is reset to a round in $[\mathrm{repT}_i, t]$ minimizing $W$ and the adversary chooses new valid stretch values for level $i$.
5. A completing round ends; a continuing round returns to stage 3.

The value of the game is the pair of tuples $(s_0, \ldots, s_d)$ and $(r_0, \ldots, r_d)$, where $s_i$ counts the player's $\mathrm{shift}(i)$ steps and $r_i$ the adversary's $\mathrm{rebuild}(i)$ steps.

## Depends on

- [Tree chains with shifts and rebuilds over recursive sparsified core graphs](../dynamic-min-ratio-cycle-data-structures/shifted-tree-chain.md)

## Sources

- Jan van den Brand, Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, Aaron Sidford, "A Deterministic Almost-Linear Time Algorithm for Minimum-Cost Flow", FOCS (2023), arXiv:2309.16629.
