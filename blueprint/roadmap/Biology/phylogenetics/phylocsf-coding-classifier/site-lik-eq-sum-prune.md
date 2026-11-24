# Site likelihood by Felsenstein's pruning algorithm

For every tree $t$, root distribution $\pi$ and column $\mathrm{col}$, the [site likelihood](site-lik.md) equals $\sum_{s} \pi(s)\, \mathrm{pr}(t, s)$, where $\mathrm{pr}$ is the [pruning recursion](../felsenstein-s-pruning-algorithm/prune.md) for the [leaf data](leaf-data.md) of $\mathrm{col}$.
