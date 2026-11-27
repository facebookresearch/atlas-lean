# Fractional edge cover number equals fractional independence number

Let $q = R_1 \bowtie \dots \bowtie R_n$ be a join query with hypergraph $H_q$. The linear program that minimizes the weight of a
[fractional edge cover](../join-processing/natural-join-queries-their-hypergraphs-and-fractional-edge-c.md) of $H_q$ and the linear program that
maximizes the weight of a [fractional independent set](fractional-independent-sets-of-a-hypergraph.md) of $H_q$ are dual to
each other. Consequently a minimal fractional edge cover and a maximal fractional independent set of $H_q$ have the same
weight, so $\rho^*(H_q)$ equals the fractional independence number of $H_q$.

## Depends on

- [Natural join queries, their hypergraphs and fractional edge covers](../join-processing/natural-join-queries-their-hypergraphs-and-fractional-edge-c.md)
- [Fractional independent sets of a hypergraph](fractional-independent-sets-of-a-hypergraph.md)

## Proof depends on

- [Strong linear programming duality](../../../Geometry/convex-geometry/linear-programming/strong-linear-programming-duality.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, the linear programs $EC(H_q)$ and $IS(H_q)$, Theorem 25.18 (strong duality, stated) and Corollary 25.19 (pp. 219–220).
