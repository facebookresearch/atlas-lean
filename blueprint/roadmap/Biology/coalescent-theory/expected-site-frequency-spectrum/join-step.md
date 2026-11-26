# Transition operator of random joining

For a real function $g$ on lists of natural numbers, its image under the random-joining operator is the function whose value at a list $b$ is

- $g$ of the empty list, if $b$ has fewer than two entries;
- otherwise, the average of $g(b')$ over the lists $b'$ obtained from $b$ by [merging the blocks](merge-blocks.md) at positions $i < j$, over all such pairs of positions.

Its $j$-th iterate at $b$ is the expectation of $g$ at step $j$ of random joining started from $b$, where the empty list stands for the steps after the process has stopped (see [Random joining has finite support and iterates the join step](exists-finset-random-joining.md)).
