# Ahn-Guha-McGregor linear sketches recover a spanning forest from dynamic graph streams

There is a distribution over linear sketches of the edge-indicator vector of an $n$-vertex graph, of total size $O(n \log^3 n)$ bits, from which a spanning forest of the final graph (hence its connected components) can be computed with high probability, for any dynamic graph stream fixed independently of the sketch's randomness. Analogous linear sketches with $O(n\,\mathrm{polylog}\,n)$ bits decide $k$-edge-connectivity for constant $k$ and bipartiteness. If the final graph is connected (as assumed in Ahn–Guha–McGregor, Section 3.4; a disconnected graph has no spanning tree) and its edge weights lie in $[1, W]$, running the connectivity sketch on the subgraphs of edges of weight at most $(1 + \varepsilon)^i$ for each of the $\lceil\log_{1+\varepsilon} W\rceil$ thresholds approximates the minimum spanning tree weight within a factor $1 + \varepsilon$; when $W = \mathrm{poly}(n)$ this is a single-pass algorithm in $O(\varepsilon^{-1} n \log^3 n)$ space, and for larger $W$ the number of thresholds grows with $\log W$.

## Proof sketch

For each vertex $v$ keep $O(\log n)$ independent $L_0$-sampler sketches of $a_v$, each of $O(\log^2 n)$ bits. Run Borůvka's algorithm on the sketches: in each round, for every current component $S$, add the sketches of its vertices to obtain a sketch of $\sum_{v \in S} a_v$, whose support is the cut $\delta(S)$, and sample one cut edge, merging components as in union-find. Each round decreases the difference between the number of current components and the number of connected components of the final graph by at least a third in expectation, so $O(\log n)$ rounds suffice, each using a fresh sketch, since reusing a sketch would make the queries depend on its own earlier answers.

## Depends on

- [Semi-streaming graph model with insertion-only, dynamic and random-order edge streams](../semi-streaming-matching-and-vertex-cover/semi-streaming-graph-model.md)
- [Turnstile streams, support size and linear sketches of a frequency vector](turnstile-streams-and-support-size.md)
- [Spanning forest of an input graph](../../../graph-algorithms/spanning-trees-flows-matchings/kruskal-s-algorithm/is-spanning-forest.md)

## Proof depends on

- [Signed vertex-incidence vectors sum to the indicator of a cut](signed-incidence-vectors-cancel-inside-cuts.md)
- [Jowhari-Sağlam-Tardos samplers: zero-relative-error L0 sampling in O(log^2 n) bits](l0-sampler-with-log-squared-bits.md)
- [Connected components via union-find](../../../data-structures/disjoint-sets-and-dynamic-trees/disjoint-set-data-structure/connected-components.md)

## Sources

- Kook Jin Ahn, Sudipto Guha, Andrew McGregor, "Analyzing Graph Structure via Linear Measurements", SODA (2012), Section 3.4 and Theorem 3.4.
- Hossein Jowhari, Mert Sağlam, Gábor Tardos, "Tight Bounds for Lp Samplers, Finding Duplicates in Streams, and Related Problems", PODS (2011), arXiv:1012.4889.
