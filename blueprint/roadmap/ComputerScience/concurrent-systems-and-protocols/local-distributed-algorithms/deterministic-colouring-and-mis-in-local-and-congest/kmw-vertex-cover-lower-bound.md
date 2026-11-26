# Locality lower bound for approximating minimum vertex cover

Let $G = (V, E)$ be a simple connected graph with $n$ vertices and maximum degree $\Delta$, whose vertices carry distinct identifiers from $\{1, \dots, n^{O(1)}\}$. Every randomized LOCAL algorithm computing a constant-factor (or even polylogarithmic-factor) approximation of minimum vertex cover, or of minimum dominating set or maximum matching, requires $\Omega\bigl(\min\{\sqrt{\log n / \log\log n},\; \log \Delta / \log\log \Delta\}\bigr)$ rounds on some graph. The same lower bound applies to maximal independent set and maximal matching, which yield $2$-approximate vertex covers.

## Proof sketch

Construct cluster-tree graphs in which two classes of vertices, $C_0$ and $C_1$, have isomorphic radius-$t$ neighbourhoods for $t$ below the bound, while $C_0$ is much larger than $C_1$ and an optimal vertex cover uses only small classes. Indistinguishability forces any $t$-round algorithm to treat $C_0$ and $C_1$ alike, so it must include many vertices of the large class to cover the edges between them, which yields a large approximation ratio; high girth of the construction relative to $t$ makes the neighbourhoods tree-like and isomorphic.

## Depends on

- [The LOCAL model](../../distributed-execution-models/the-local-model.md)
- [Dominating set](../../../../GraphTheory/independence-and-domination/dominating-sets/is-dominating.md)

## Sources

- F. Kuhn, T. Moscibroda, R. Wattenhofer, "Local Computation: Lower and Upper Bounds", Journal of the ACM 63(2) (2016).
