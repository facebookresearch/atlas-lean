# Correctness of the Stoer-Wagner minimum cut algorithm

The **Stoer-Wagner algorithm** on a weighted multigraph with $n \ge 2$ vertices and nonnegative integer weights runs $n - 1$ phases; each phase computes an MA ordering of the current super-vertices, records the cut of the phase (the weight around the last super-vertex $t$) and merges $t$ into the second-to-last super-vertex. The minimum recorded cut, with its vertex set, is a global minimum cut of the graph. It is deterministic and uses no flow computations.

## Proof sketch

By the pendent pair lemma, either some global minimum cut separates the pendent pair, in which case the phase cut is minimum, or none does, in which case merging preserves the minimum.

## Depends on

- [Maximum adjacency orderings](maximum-adjacency-ordering.md)
- [Minimum cut size](../../../randomized-algorithms/karger-s-algorithm/is-min-cut.md)

## Proof depends on

- [The last vertex of an MA ordering is a minimum cut for the pendent pair](pendent-pair-lemma.md)

## Sources

- M. Stoer and F. Wagner, "A Simple Min-Cut Algorithm", Journal of the ACM 44(4), 1997.
