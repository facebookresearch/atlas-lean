# Locality lower bound for approximating minimum vertex cover

Let $G = (V, E)$ be a simple connected graph with $n$ vertices and maximum degree $\Delta$, whose vertices carry distinct identifiers from $\{1, \dots, n^{O(1)}\}$. For every integer $k > 0$ there are graphs on which every $k$-round, possibly randomized, LOCAL algorithm for minimum vertex cover has (expected) approximation ratio at least $\Omega\bigl(n^{(1 - o(1))/(4k^2)}/k\bigr)$ and at least $\Omega\bigl(\Delta^{1/(k+1)}/k\bigr)$; the same holds for minimum dominating set and for (fractional) maximum matching. Consequently, obtaining a constant or polylogarithmic approximation ratio for any of these problems requires $\Omega\bigl(\sqrt{\log n / \log\log n}\bigr)$ rounds and $\Omega(\log \Delta / \log\log \Delta)$ rounds on suitable graphs, even when identifiers are $\{1, \dots, n\}$ and every vertex knows the whole topology. The same two lower bounds hold for the expected running time of every possibly randomized algorithm that always outputs a maximal matching, whose matched vertices form a $2$-approximate vertex cover, and hence for maximal independent set, since a maximal matching is a maximal independent set of the line graph.

## Proof sketch

Construct cluster-tree graphs in which two classes of vertices, $C_0$ and $C_1$, have isomorphic radius-$k$ neighbourhoods, while $C_0$ is much larger than $C_1$ and an optimal vertex cover uses only small classes. Indistinguishability forces any $k$-round algorithm to treat $C_0$ and $C_1$ alike, so it must include many vertices of the large class to cover the edges between them, which yields a large approximation ratio; high girth of the construction relative to $k$ makes the neighbourhoods tree-like and isomorphic. For maximal matching, an algorithm with expected running time $T$ is turned into a vertex cover algorithm with fixed running time $2T + 1$ and constant expected approximation ratio, and the line graph transfers the bound to MIS with the same asymptotics in $n$ and $\Delta$.

## Depends on

- [The LOCAL model](../../distributed-execution-models/the-local-model.md)
- [Dominating set](../../../../GraphTheory/independence-and-domination/dominating-sets/is-dominating.md)

## Sources

- F. Kuhn, T. Moscibroda, R. Wattenhofer, "Local Computation: Lower and Upper Bounds", Journal of the ACM 63(2) (2016), arXiv:1011.5470, Theorems 13, 14, 20, 22 and 23 and Corollary 16.
