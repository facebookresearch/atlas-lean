# Symmetric network congestion games admit polynomial-time pure equilibria

In a symmetric network congestion game, where all $k$ players choose paths between a common source $s$ and sink $t$ of a directed graph and every edge has a nondecreasing delay function, a pure Nash equilibrium can be computed in polynomial time by computing a minimum-cost integral flow of value $k$ in the graph obtained by replacing each edge $e$ by $k$ parallel unit-capacity edges with costs $d_e(1), d_e(2), \dots, d_e(k)$, the marginal increments of Rosenthal's potential.

## Proof sketch

Rosenthal's potential of a profile equals $\sum_e \sum_{j=1}^{x_e} d_e(j)$, which is the cost of the corresponding integral flow in the expanded graph because nondecreasing delays make the cheapest use of the parallel copies take them in order. A minimum-cost flow therefore minimizes the potential globally, and its decomposition into $k$ paths is a pure Nash equilibrium since potential minimizers are equilibria.

## Depends on

- [Congestion game](../../potential-games/congestion-game.md)
- [Rosenthal's potential](../../potential-games/potential.md)
- [Pure Nash equilibrium](../../potential-games/is-pure-nash.md)

## Proof depends on

- [Rosenthal's theorem](../../potential-games/is-exact-potential-potential.md)

## Sources

- A. Fabrikant, C. Papadimitriou, K. Talwar, "The Complexity of Pure Nash Equilibria", STOC 2004.
