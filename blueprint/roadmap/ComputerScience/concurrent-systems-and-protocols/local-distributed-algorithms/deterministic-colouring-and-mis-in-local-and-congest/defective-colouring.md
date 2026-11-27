# Defective colouring

Let $G = (V, E)$ be a simple connected graph with $n$ vertices and maximum degree $\Delta$, whose vertices carry distinct identifiers from $\{1, \dots, n^{O(1)}\}$. For an integer $d \ge 0$, a $d$-defective $k$-colouring is a map $c : V \to \{1, \dots, k\}$ such that every vertex has at most $d$ neighbours of its own colour; a proper colouring is $0$-defective. Every graph has a $d$-defective $\bigl\lceil (\Delta + 1)/(d + 1) \bigr\rceil$-colouring: among all colourings with this many colours, one minimizing the number of monochromatic edges has defect at most $d$, since a vertex with more than $d$ same-coloured neighbours has a colour class with at most $d$ of its neighbours and recolouring strictly decreases monochromatic edges.

## Depends on

- [The (deg + 1)-list-coloring problem (D1LC)](../../../randomized-algorithms/palette-sparsification-and-sublinear-coloring/degree-plus-one-list-coloring.md)

## Sources

- L. Lovász, "On decomposition of graphs", Studia Scientiarum Mathematicarum Hungarica 1 (1966).
- F. Kuhn, "Weak Graph Colorings: Distributed Algorithms and Applications", SPAA 2009.
