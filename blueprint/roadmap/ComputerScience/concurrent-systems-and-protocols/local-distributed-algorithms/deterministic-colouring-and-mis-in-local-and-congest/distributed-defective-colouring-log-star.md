# Distributed defective colouring in O(log* n) rounds

Let $G = (V, E)$ be a simple connected graph with $n$ vertices and maximum degree $\Delta$, whose vertices carry distinct identifiers from $\{1, \dots, n^{O(1)}\}$. For every integer $1 \le d \le \Delta$, a $d$-defective $O\bigl((\Delta/d)^2\bigr)$-colouring can be computed deterministically in $O(\log^* n)$ rounds of the LOCAL model, and in $O(\log^* n)$ rounds of CONGEST. As a consequence, $(\Delta + 1)$-colouring can be computed deterministically in $O(\Delta + \log^* n)$ rounds by recursively splitting the graph into low-degree subgraphs with disjoint palettes.

## Proof sketch

Generalize Linial's colour reduction with set systems that are cover-free in a defective sense: a vertex chooses a new colour from its colour's set that lies in at most $d$ of its neighbours' sets, which exists when each set has size about $(\Delta/d)^2 \log k$ and the sets pairwise intersect little. Iterating $O(\log^* n)$ times gives $O((\Delta/d)^2)$ colours. For $(\Delta+1)$-colouring, use $d = \Delta/2$ defective colourings to split into $O(1)$ subgraphs of half the degree, recurse with palettes of proportional sizes, and finish by local corrections.

## Depends on

- [Defective colouring](defective-colouring.md)

## Proof depends on

- [Linial's colour reduction to O(Delta^2) colours in O(log* n) rounds](linial-colour-reduction.md)

## Sources

- F. Kuhn, "Weak Graph Colorings: Distributed Algorithms and Applications", SPAA 2009.
- L. Barenboim, M. Elkin, F. Kuhn, "Distributed (Delta+1)-Coloring in Linear (in Delta) Time", SIAM Journal on Computing 43(1) (2014); STOC 2009.
