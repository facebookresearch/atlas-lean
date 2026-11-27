# Price Sampling Algorithm: 4d-competitive secretary on transversal matroids

Let $G \subseteq L \times R$ be a bipartite graph in which every left vertex has degree at most $d$, $|L| \ge 2$, with nonnegative well-behaved weights on $L$; left vertices arrive in uniformly random order. The *Price Sampling Algorithm* observes the first $\lceil |L|/2 \rceil$ arrivals, gives each right vertex the price equal to the largest weight of a sampled neighbor (or $0$), and matches each later arrival $l$ to an unmatched neighbor of lowest price that is strictly below $w(l)$, if any. It always outputs a matching of $G$, and for every matching $M$ of $G$,

$$
\sum_{(l, r) \in M} w(l) \le 4d\;\mathbb{E}[\text{weight matched}].
$$

## Proof sketch

For each right vertex consider its heaviest neighbor; with probability at least $1/4$ this neighbor arrives after the sample while the second-heaviest is sampled, so it finds the vertex priced below its weight. Each matched element blocks at most $d$ right vertices, and charging the optimal matching's weight to the heaviest neighbors gives the factor $4d$.

## Depends on

- [Matroid secretary problem](matroid-secretary-problem.md)
- [Matching in a bipartite graph](../../graph-algorithms/spanning-trees-flows-matchings/maximum-bipartite-matching/is-matching.md)

## Proof depends on

- [Matroid secretary problem](matroid-secretary-problem.md)

## Sources

- Moshe Babaioff, Nicole Immorlica and Robert Kleinberg, "Matroids, Secretary Problems, and Online Mechanisms", Proceedings of the 18th ACM-SIAM Symposium on Discrete Algorithms (SODA), 2007.
