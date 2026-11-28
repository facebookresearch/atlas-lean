# Gomory-Hu trees of unweighted graphs with polylogarithmically many max-flows

Let $G$ be a connected undirected unweighted multigraph with $n$ vertices and $m$ edges. Connectivity is needed for the output to be a cut-equivalent tree in the positive-weight sense: two vertices in different components have minimum cut value $0$, which no path of a tree with positive edge weights realizes as a minimum edge weight. For a disconnected $G$ one runs the algorithms on each connected component (found in $O(n + m)$ time) and joins the component trees by $c - 1$ edges of weight $0$ between $c$ components, an $O(n)$ overhead; the result represents all pairwise minimum cut values but has zero-weight edges.

1. (Abboud-Krauthgamer-Trabelsi) If $G$ is simple, a cut-equivalent tree of $G$ can be computed by a randomized (Monte Carlo) algorithm in $n^{2+o(1)}$ time, correct with probability $1 - n^{-c}$; deterministically in $\tilde O(n^{8/3})$ time.
2. (Abboud-Krauthgamer-Li-Panigrahi-Saranurak-Trabelsi) A cut-equivalent tree of $G$ can be computed by a randomized (Monte Carlo) algorithm in $m^{1+o(1)}$ time plus $\mathrm{polylog}(n)$ max-flow calls on graphs with $n$ vertices and $O(m)$ edges (Table 1: $m^{1+o(1)} + \mathrm{polylog}(n) \cdot T(n, m)$); with the almost-linear maximum-flow algorithm this takes $m^{1+o(1)}$ time.

In both cases the single-source minimum cut values from any source are obtained within the same bounds.

## Proof sketch

Both algorithms pick a source (pivot) and compute, with isolating-cut calls applied to randomly subsampled terminal sets at geometric rates, the minimal minimum cuts separating the pivot from many terminals at once. Every such cut is a valid split in the Gomory-Hu recursion, and the subsampling guarantees that a constant fraction of the vertices are split off at each level with high probability, so the recursion has polylogarithmic depth. In unweighted graphs the instance sizes shrink geometrically, which bounds the total size of all max-flow instances by a polylogarithmic multiple of $m$.

## Depends on

- [Single-source minimum cut values](single-source-minimum-cut-values.md)
- [Flow-equivalent and cut-equivalent trees of weighted graphs](../../../../../GraphTheory/paths-cycles-connectivity/cactus-representation-and-sparse-certificates/flow-equivalent-and-cut-equivalent-trees.md)
- [Maximum-flow oracles and the max-flow call model for cut problems](max-flow-oracle-call-model.md)

## Proof depends on

- [Isolating cut lemma with logarithmically many max-flow calls](isolating-cut-lemma.md)
- [Terminal subsampling isolates one side of a Steiner minimum cut](terminal-subsampling-isolates-steiner-cut.md)

## Sources

- Amir Abboud, Robert Krauthgamer, Ohad Trabelsi, "APMF < APSP? Gomory-Hu Tree for Unweighted Graphs in Almost-Quadratic Time", FOCS (2021), arXiv:2106.02981.
- Amir Abboud, Robert Krauthgamer, Ohad Trabelsi, "Subcubic Algorithms for Gomory-Hu Tree in Unweighted Graphs", STOC (2021), arXiv:2012.10281.
- Amir Abboud, Robert Krauthgamer, Jason Li, Debmalya Panigrahi, Thatchaphol Saranurak, Ohad Trabelsi, "Breaking the Cubic Barrier for All-Pairs Max-Flow: Gomory-Hu Tree in Nearly Quadratic Time", FOCS (2022), arXiv:2111.04958, Theorem 1.4 and Table 1.
