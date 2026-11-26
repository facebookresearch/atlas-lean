# Minimum spanning trees in O(1) rounds of the congested clique, deterministically

In the congested clique, a minimum spanning tree (forest) of an $n$-vertex weighted input graph with weights of $O(\log n)$ bits can be computed in $O(1)$ rounds: first by a randomized algorithm, and subsequently by a deterministic algorithm. Earlier deterministic bounds were $O(\log\log n)$ rounds via Borůvka-style merging with fragment-size squaring.

## Proof sketch

Reduce the number of components quickly by Borůvka-style contraction until the contracted graph has about $n / \mathrm{poly}\log n$ vertices, then sparsify: the randomized algorithm samples edges so that the remaining edges that can belong to the MST (the $F$-light edges with respect to a sampled forest) number $O(n)$, which can be routed to a single processor by Lenzen routing. The deterministic algorithm replaces sampling by a derandomized construction of sparse certificate-like edge subsets using limited-independence hash functions and the method of conditional expectations.

## Depends on

- [The congested clique model](the-congested-clique-model.md)
- [Prim's algorithm returns a minimum spanning tree](../../../graph-algorithms/spanning-trees-flows-matchings/prim-s-algorithm/prim-minimum-spanning-tree.md)

## Proof depends on

- [Lenzen's deterministic constant-round routing and sorting in the congested clique](congested-clique-constant-round-routing.md)

## Sources

- T. Jurdziński, K. Nowicki, "MST in O(1) Rounds of Congested Clique", SODA 2018, arXiv:1707.08484.
- K. Nowicki, "A Deterministic Algorithm for the MST Problem in Constant Rounds of Congested Clique", STOC 2021, arXiv:1912.04239.
- Z. Lotker, B. Patt-Shamir, E. Pavlov, D. Peleg, "Minimum-Weight Spanning Tree Construction in O(log log n) Communication Rounds", SIAM Journal on Computing 35(1) (2005); SPAA 2003.
