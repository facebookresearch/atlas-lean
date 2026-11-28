# Fully dynamic connectivity, spanning forest and minimum spanning forest problems

Fix a vertex set $V$ with $|V| = n$ and start from the edgeless graph $G_0 = (V, \emptyset)$. An online sequence of operations is processed: $\mathrm{Insert}(u, v)$ adds an edge, $\mathrm{Delete}(u, v)$ removes an existing edge, and $\mathrm{Connected}(u, v)$ asks whether $u$ and $v$ lie in the same connected component of the current graph $G_t$. Restricted versions require the graph to remain a forest, or a disjoint union of paths, at all times.

1. *Fully dynamic connectivity* answers all $\mathrm{Connected}$ queries.
2. *Dynamic spanning forest* must, after every update, store explicitly a spanning forest $F_t$ of $G_t$ (a forest with the same connected components as $G_t$) and report the edges entering or leaving $F_t$; the change per update is $O(1)$ edges.
3. *Dynamic minimum spanning forest (MSF)* receives a weight $w(e)$ with each inserted edge and must maintain $F_t$ as a minimum spanning forest of $(G_t, w)$.

Costs are measured on the word RAM with words of $\Theta(\log n)$ bits, per operation, as update and query time.

## Depends on

- [Dynamic graph problems](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/dynamic-graph-problems.md)
- [Spanning forest of an input graph](../../../graph-algorithms/spanning-trees-flows-matchings/kruskal-s-algorithm/is-spanning-forest.md)
- [Connected components via union-find](../disjoint-set-data-structure/connected-components.md)
- [The word-RAM model](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Sources

- Jacob Holm, Kristian de Lichtenberg, Mikkel Thorup, "Poly-logarithmic deterministic fully-dynamic algorithms for connectivity, minimum spanning tree, 2-edge, and biconnectivity", J. ACM 48(4) (2001).
- Monika Henzinger, Sebastian Krinninger, Danupon Nanongkai, Thatchaphol Saranurak, "Unifying and Strengthening Hardness for Dynamic Problems via the Online Matrix-Vector Multiplication Conjecture", STOC (2015), arXiv:1511.06773.
