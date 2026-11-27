# One-inclusion graph and the one-inclusion graph predictor

For a finite index set $\iota$ and a set $S \subseteq \{0,1\}^{\iota}$ of labelings, the one-inclusion graph of $S$ has vertex set $S$ and an edge between $f, g \in S$ whenever $f$ and $g$ differ in exactly one coordinate $i \in \iota$ (the edge is said to be in direction $i$). An orientation assigns to each edge one of its endpoints as its tail; the outdegree of a vertex is the number of edges of which it is the tail.

For a binary class $C$ on a domain $X$, the one-inclusion graph predictor receives a sample $((x_1, y_1), \dots, (x_m, y_m))$ realizable by $C$ and a test point $x$. If $x = x_j$ for some $j$ it predicts $y_j$. Otherwise it forms $U = \{x_1, \dots, x_m, x\}$, the set of labelings of $U$ realized by $C$, and its one-inclusion graph with a fixed orientation of outdegree at most $\mathrm{VCdim}(C|_U)$; if all realized labelings consistent with the sample agree at $x$ it predicts that common label, and otherwise the two consistent labelings form an edge in direction $x$, and it predicts the label of the head of that edge.

## Depends on

- [The VC dimension is at most the size of the ground set](../../../../../Combinatorics/extremal-set-theory/vc-dim-le-card.md)

## Sources

- D. Haussler, N. Littlestone and M. K. Warmuth, "Predicting {0, 1}-Functions on Randomly Drawn Points", Information and Computation, 1994.
