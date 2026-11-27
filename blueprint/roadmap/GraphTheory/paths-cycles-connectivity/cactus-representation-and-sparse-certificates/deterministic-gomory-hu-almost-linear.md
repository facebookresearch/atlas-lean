# Deterministic almost-linear-time Gomory-Hu trees

There is a deterministic algorithm that, given an undirected graph with $n$ vertices, $m$ edges and polynomially bounded positive integer weights, computes a cut-equivalent tree in $m^{1+o(1)}$ time. In particular, for every $k$ the $k$-edge-connected components (the classes of the relation $\lambda_G(u,v) \ge k$) are computable deterministically in $m^{1+o(1)}$ time; previously the best deterministic bound for a cut-equivalent tree was $n \cdot m^{1+o(1)}$, from the original Gomory-Hu reduction with $n - 1$ maximum flows.

## Proof sketch

The randomized almost-linear algorithms sample a pivot vertex, which yields Gomory-Hu recursion of polylogarithmic depth, and sample guide trees from a packing of Steiner trees. Both are replaced by deterministic components: a deterministic reduction from all-pairs mincuts to single-source mincuts with only subpolynomial overhead, and a deterministic almost-linear-time algorithm for single-source mincuts. Deterministic almost-linear maximum flow supplies the max-flow oracle.

## Depends on

- [Flow-equivalent and cut-equivalent trees of weighted graphs](flow-equivalent-and-cut-equivalent-trees.md)

## Proof depends on

- [Gomory-Hu trees in almost-linear time: all-pairs max-flow reduces to single-pair max-flow](gomory-hu-trees-almost-linear-time.md)
- [Deterministic Steiner minimum cut in maximum-flow time (Ding-Li)](../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/almost-linear-flows-cuts-and-dynamic-matching/isolating-cuts-and-steiner-min-cuts/ding-li-steiner-cut-in-max-flow-time.md)
- [Isolating cut lemma with logarithmically many max-flow calls](../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/almost-linear-flows-cuts-and-dynamic-matching/isolating-cuts-and-steiner-min-cuts/isolating-cut-lemma.md)

## Sources

- Amir Abboud, Rasmus Kyng, Jason Li, Debmalya Panigrahi, Maximilian Probst Gutenberg, Thatchaphol Saranurak, Weixuan Yuan, Wuwei Yuan, "Deterministic Almost-Linear-Time Gomory-Hu Trees", FOCS (2025), arXiv:2507.20354.
- Amir Abboud, Jason Li, Debmalya Panigrahi, Thatchaphol Saranurak, "All-Pairs Max-Flow is no Harder than Single-Pair Max-Flow: Gomory-Hu Trees in Almost-Linear Time", FOCS (2023).
