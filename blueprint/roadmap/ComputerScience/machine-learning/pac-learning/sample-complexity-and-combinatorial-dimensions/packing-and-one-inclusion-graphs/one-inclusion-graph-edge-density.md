# Edge density and bounded-outdegree orientations of one-inclusion graphs

Let $\iota$ be finite and let $S \subseteq \{0,1\}^{\iota}$ shatter no set of more than $d$ coordinates. Then the one-inclusion graph of $S$ has at most $d\,|S|$ edges. Since every subset of $S$ inherits the same shattering bound, every induced subgraph on $U \subseteq S$ has at most $d\,|U|$ edges, and hence the edges of the one-inclusion graph of $S$ can be oriented so that every vertex has outdegree at most $d$.

## Proof sketch

The edge bound is proved by induction on $|\iota|$ via the shifting (compression) operation, which does not decrease the number of edges and preserves the shattering bound, reducing to down-closed families where each vertex has at most $d$ downward edges. The orientation follows from the density bound for all induced subgraphs by Hakimi's theorem, which is a consequence of Hall's marriage theorem applied to the bipartite graph between edges and $d$ copies of each vertex.

## Depends on

- [One-inclusion graph and the one-inclusion graph predictor](one-inclusion-graph-predictor.md)

## Sources

- D. Haussler, N. Littlestone and M. K. Warmuth, "Predicting {0, 1}-Functions on Randomly Drawn Points", Information and Computation, 1994.
- D. Haussler, "Sphere Packing Numbers for Subsets of the Boolean n-Cube with Bounded Vapnik-Chervonenkis Dimension", Journal of Combinatorial Theory, Series A, 1995.
