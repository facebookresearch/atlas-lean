# Undirected vertex connectivity with polylogarithmically many max-flows

Let $\kappa(G)$ be the vertex connectivity of an undirected graph $G$ with $n$ vertices and $m$ edges: the least number of vertices whose removal disconnects $G$ or leaves a single vertex. If a maximum flow in graphs with $m$ edges can be computed in $O(m^{\alpha})$ time for some $\alpha \ge 1$, then $\kappa(G)$ can be computed by a randomized algorithm in $\tilde O(m^{\alpha})$ time with success probability $1 - n^{-c}$. With an $m^{4/3+o(1)}$-time maximum-flow algorithm this gives $m^{4/3+o(1)}$ time; for directed graphs the corresponding reduction gives $m n^{1 - 1/12 + o(1)}$ time.

## Proof sketch

Fix a minimum vertex cut $N$ splitting $V \setminus N$ into $L$ and the rest. If $|L|$ is small relative to the degrees, random sampling of a source in $L$ and local flow computations find $N$; otherwise a random terminal set $T$ hits $L$ in exactly one vertex $x$ with good probability, and then the minimum vertex cut separating $x$ from $T \setminus \{x\}$ is a global minimum vertex cut. All such $(x, T \setminus \{x\})$ vertex cuts are found by a vertex version of the isolating cut lemma, obtained via vertex splitting and Menger's theorem, with $O(\log n)$ max-flow calls; repeating over polylogarithmically many sampling rates gives the bound.

## Depends on

- [Maximum-flow oracles and the max-flow call model for cut problems](max-flow-oracle-call-model.md)
- [$k$-vertex-connected graph](../../../../../GraphTheory/paths-cycles-connectivity/vertex-connectivity/is-vertex-connected.md)

## Proof depends on

- [Isolating cut lemma with logarithmically many max-flow calls](isolating-cut-lemma.md)
- [Menger's theorem for vertex cuts and internally disjoint paths](../../../../../GraphTheory/paths-cycles-connectivity/menger-s-theorem/menger-vertex-max-min.md)
- [Vertex cuts separating two vertices](../../../../../GraphTheory/paths-cycles-connectivity/menger-s-theorem/is-stvertex-cut.md)

## Sources

- Jason Li, Danupon Nanongkai, Debmalya Panigrahi, Thatchaphol Saranurak, Sorrachai Yingchareonthawornchai, "Vertex Connectivity in Poly-logarithmic Max-flows", STOC (2021), arXiv:2104.00104.
