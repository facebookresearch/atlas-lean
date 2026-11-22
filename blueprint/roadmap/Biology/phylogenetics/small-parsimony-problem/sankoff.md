# Sankoff's algorithm

For observed states $\sigma$, a tree $t$ with costs and a state $s$, Sankoff's cost $\mathrm{Sk}(t, s)$ is the [pruning recursion](../felsenstein-s-pruning-algorithm/prune.md) over the [cost semiring](cost.md) with the [tropical leaf weights](leaf-obs.md) of $\sigma$: the minimum cost of the subtree given state $s$ at its root.
