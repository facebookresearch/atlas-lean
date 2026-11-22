# Correctness of the zero-one knapsack algorithm

For every list of knapsack items and every
capacity $W \in \mathbb{N}$, let $S$ and $v$ be the index set and the reported value returned by
the bottom-up knapsack algorithm. Then $S$ is feasible for $W$, $v$ is the total value of $S$,
and every feasible set $T$ of item indices has total value at most $v$.
