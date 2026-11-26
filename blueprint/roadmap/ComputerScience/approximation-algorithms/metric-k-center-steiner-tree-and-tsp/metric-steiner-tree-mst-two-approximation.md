# The terminal MST is a 2-approximation for metric Steiner tree

Let $d$ be a symmetric cost satisfying the triangle inequality on a finite set containing a terminal set $R$. A minimum spanning tree of the complete graph on $R$ with costs $d$ costs at most twice the minimum cost of a tree connecting $R$ that may use other (Steiner) points.

## Proof sketch

Double an optimal Steiner tree to get a closed walk visiting all terminals of cost $2\,\mathrm{OPT}$; shortcutting Steiner points and repeated terminals gives a spanning tree (indeed a Hamiltonian path) on $R$ of no larger cost.

## Depends on

- [Steiner tree instances](../../../TheoryOfComputation/np-completeness/paths-cycles-and-subgraphs/steiner-tree/steiner-tree-instance.md)
- [Kruskal's algorithm gives a minimum spanning forest](../../graph-algorithms/spanning-trees-flows-matchings/kruskal-s-algorithm/kruskal-minimal.md)

## Proof depends on

- [Kruskal's algorithm gives a minimum spanning forest](../../graph-algorithms/spanning-trees-flows-matchings/kruskal-s-algorithm/kruskal-minimal.md)

## Sources

- E. N. Gilbert and H. O. Pollak, "Steiner Minimal Trees", SIAM Journal on Applied Mathematics 16(1), 1968.
- D. P. Williamson and D. B. Shmoys, "The Design of Approximation Algorithms", Cambridge University Press, 2011.
