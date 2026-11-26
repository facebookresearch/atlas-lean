# Minimum vertex separators by vertex splitting

Given a simple graph $G$ on $n$ vertices and vertex sets $Z$, $A$, $B$, a set $X$ of vertices outside $Z$ of minimum size such that $Z \cup X$ separates $A$ from $B$ (every $A$-$B$ path meets $Z \cup X$) can be computed by one maximum-flow computation on the network obtained by splitting every vertex $v \notin Z$ into $v_{\mathrm{in}} \to v_{\mathrm{out}}$ of capacity $1$, with infinite-capacity arcs for the edges of $G - Z$; the minimum separator is read off a minimum cut, and its size equals the maximum number of pairwise vertex-disjoint $A \setminus Z$-$B \setminus Z$ paths in $G - Z$. With dense augmenting paths this takes $O(n^5)$ word-RAM instructions, and the program also outputs a side labelling certifying the separation.

## Proof sketch

Unit vertex capacities (on every vertex outside $Z$, terminals included) turn vertex-disjoint paths into a flow and vertex separators into finite cuts; Menger's theorem is the integral max-flow min-cut theorem on this network.

## Depends on

- [Vertex cuts separating two vertices](../../../../GraphTheory/paths-cycles-connectivity/menger-s-theorem/is-stvertex-cut.md)
- [The word-RAM model](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Proof depends on

- [Max-flow min-cut theorem](../../../../GraphTheory/matchings-and-flows/max-flow-min-cut-theorem/max-flow-min-cut.md)
- [Edmonds-Karp computes a maximum flow and a minimum cut](../edmonds-karp-algorithm/edmonds-karp-max-flow-min-cut.md)

## Sources

- K. Menger, "Zur allgemeinen Kurventheorie", Fundamenta Mathematicae 10, 1927.
- L. R. Ford Jr. and D. R. Fulkerson, "Flows in Networks", Princeton University Press, 1962.
- A. Schrijver, "Combinatorial Optimization: Polyhedra and Efficiency", Springer, 2003.
