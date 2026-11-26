# Gomory-Hu trees on the word RAM

There is a single deterministic word-RAM program that, given an $n$-vertex undirected multigraph by its symmetric weight matrix with nonnegative integer weights, outputs a weighted Gomory-Hu tree (parent array and edge weights) by Gusfield's algorithm with dense Edmonds-Karp maximum flow as the cut oracle, in time $n - 1$ times the cost of one dense maximum-flow computation, i.e. $O(n^6)$ instructions, at word sizes large enough for the total weight and $O(n^2)$ addresses. Push-relabel or Dinitz cut oracles may be substituted, giving correct Gomory-Hu trees as well.

## Depends on

- [Gomory-Hu trees](gomory-hu-tree.md)
- [The word-RAM model](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Proof depends on

- [Gusfield's algorithm: Gomory-Hu trees with n - 1 minimum cut computations](gusfield-algorithm.md)
- [Edmonds-Karp computes a maximum flow and a minimum cut](../edmonds-karp-algorithm/edmonds-karp-max-flow-min-cut.md)

## Sources

- D. Gusfield, "Very Simple Methods for All Pairs Network Flow Analysis", SIAM Journal on Computing 19(1), 1990.
- R. E. Gomory and T. C. Hu, "Multi-Terminal Network Flows", Journal of the Society for Industrial and Applied Mathematics 9(4), 1961.
