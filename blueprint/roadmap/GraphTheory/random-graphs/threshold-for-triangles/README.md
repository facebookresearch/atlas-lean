# Threshold for triangles

In the binomial random graph $G(n, p)$ the expected number of triangles is $\binom n3 p^3$. The first moment method shows that $G(n,p)$ has no triangle with high probability when $np \to 0$, and the second moment method, with the observation that two triangles are dependent only when they share an edge, shows that it has one with high probability when $np \to \infty$: $1/n$ is a threshold function for containing a triangle. Here $G(n,p)$ is the [graph of a random set of pairs](../../graph-ramsey-theory/graph-ramsey-numbers/pair-graph.md), each pair kept independently with probability $p$.

- [Triangles are absent below the threshold 1/n](tendsto-measure-real-not-clique-free-thr.md)
- [Triangles appear above the threshold 1/n](tendsto-measure-real-not-clique-free-thr-2.md)
- [First moment bound for triangles in G(n, p)](measure-real-not-clique-free-three-le.md)
- [Second moment bound for triangles in G(n, p)](measure-real-clique-free-three-le.md)
- [Vertex triples](triple.md)
- [Dependency graph of the triangle events](share-edge.md)
- [Two triangles sharing an edge span five edges](five-le-card-union.md)
- [A triangle shares an edge with at most 3n others](card-share-edge-le.md)

## Related topics

- [First and second moment methods](../../../Combinatorics/probabilistic-combinatorics/first-and-second-moment-methods/README.md): the general tools specialised here.
- [Janson's inequalities](../../../Combinatorics/probabilistic-combinatorics/janson-s-inequalities/README.md): the exponentially small bound $\Pr[G(n,p) \text{ is triangle-free}] \le e^{-(1+o(1))\binom n3 p^3}$ for $p = o(n^{-1/2})$.
- [Kim–Vu polynomial concentration](../../../Probability/concentration-inequalities/kim-vu-polynomial-concentration/README.md): concentration of the number of triangles itself.
