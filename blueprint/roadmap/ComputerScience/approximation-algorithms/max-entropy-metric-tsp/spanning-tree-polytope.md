# Spanning tree polytope of a connected graph

Let $G=(V,E)$ be a connected undirected multigraph with $n=|V| \ge 2$. For $S \subseteq V$ let $E(S)$ denote the set of edges with both endpoints in $S$, and for $z \in \mathbb{R}^E$ and $F \subseteq E$ write $z(F)=\sum_{e \in F} z_e$. The spanning tree polytope of $G$ is

$$
P_{\mathrm{ST}}(G)=\{z \in \mathbb{R}_{\ge 0}^{E} : z(E)=n-1,\ z(E(S)) \le |S|-1 \ \text{for all}\ \emptyset \ne S \subsetneq V\}.
$$

Edmonds showed that $P_{\mathrm{ST}}(G)$ is the convex hull of the indicator vectors $\mathbf{1}_T$ of the spanning trees $T$ of $G$ (the base polytope of the graphic matroid). Consequently, for every cost vector $c \in \mathbb{R}^E$, the minimum cost of a spanning tree equals $\min\{c^{\top}z : z \in P_{\mathrm{ST}}(G)\}$.

## Depends on

- [Kruskal's algorithm gives a minimum spanning forest](../../graph-algorithms/spanning-trees-flows-matchings/kruskal-s-algorithm/kruskal-minimal.md)
- [Basic feasible points are the extreme points](../../../Analysis/not-yet-classified/linear-programming-basic/is-basic-pt-iff-mem-extreme-points.md)

## Sources

- Jack Edmonds, "Matroids and the Greedy Algorithm", Mathematical Programming (1971).
