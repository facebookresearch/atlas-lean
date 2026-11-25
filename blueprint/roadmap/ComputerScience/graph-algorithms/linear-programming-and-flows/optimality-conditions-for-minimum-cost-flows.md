# Optimality conditions for minimum-cost flows

Let $N$ be a network with capacities and real arc costs, and $f$ a feasible flow of a given value. Then $f$ has minimum cost among feasible flows of that value if and only if the residual network $N_f$ contains no directed cycle of negative cost.

Suppose moreover that all capacities are integers. Cycle canceling, started from an integral feasible flow of an integral value $v$ and repeatedly augmenting along a negative residual cycle by its bottleneck capacity, terminates with an integral minimum-cost flow of value $v$. Successive shortest paths, started from the zero flow when $N$ has no negative-cost cycle and repeatedly augmenting along a shortest residual source–sink path by the minimum of its bottleneck capacity and the remaining amount $v$ minus the current flow value (with shortest paths computed under arbitrary real costs, for example by Bellman–Ford, or by Dijkstra's algorithm on reduced costs with respect to valid node potentials), produces after each augmentation an integral minimum-cost flow of the current value, and stops at any prescribed integral value $v$ not exceeding the maximum flow value.

## Proof depends on

- [Edmonds-Karp computes a maximum flow and a minimum cut](../spanning-trees-flows-matchings/edmonds-karp-algorithm/edmonds-karp-max-flow-min-cut.md)

## Expansion

This page becomes ready once these prerequisites are stated:

- Single-source shortest paths (proof prerequisite; not yet stated)
- The negative-cycle optimality condition for minimum-cost flows, as a page of its own
- Correctness of cycle canceling, as a page of its own
- Correctness of successive shortest paths, as a page of its own

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*, 4th ed., MIT Press, 2022
- R. K. Ahuja, T. L. Magnanti and J. B. Orlin, *Network Flows: Theory, Algorithms, and Applications*, Prentice Hall, 1993
