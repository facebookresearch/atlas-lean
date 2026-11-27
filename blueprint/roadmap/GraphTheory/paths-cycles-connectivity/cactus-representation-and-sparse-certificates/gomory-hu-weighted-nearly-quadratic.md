# Gomory-Hu trees of weighted graphs in nearly quadratic time

There is a randomized (Monte Carlo) algorithm that, given an undirected graph with $n$ vertices and positive integer edge weights bounded by $n^{O(1)}$, computes a cut-equivalent tree in $\tilde O(n^2)$ time with probability $1 - n^{-c}$. This is the first subcubic algorithm for all-pairs max-flow in general weighted graphs; under the hypothesis that all-pairs shortest paths requires $n^{3 - o(1)}$ time, it separates all-pairs max-flow from all-pairs shortest paths.

## Proof sketch

First replace $G$ by a cut sparsifier-type reduction that does not change minimum cuts between relevant pairs and has $\tilde O(n)$-size instances per recursive level. The core step computes, for a random pivot, single-source minimum cuts to many vertices using isolating cuts on terminal sets sampled at geometric rates, together with a guide-tree mechanism based on $2$-respecting cuts of a tree packing to handle weighted graphs. The resulting Gomory-Hu splits reduce the instance by a constant fraction with high probability, and the total work over $O(\log n)$ levels is $\tilde O(n^2)$.

## Depends on

- [Flow-equivalent and cut-equivalent trees of weighted graphs](flow-equivalent-and-cut-equivalent-trees.md)

## Proof depends on

- [Isolating cut lemma with logarithmically many max-flow calls](../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/almost-linear-flows-cuts-and-dynamic-matching/isolating-cuts-and-steiner-min-cuts/isolating-cut-lemma.md)
- [Gomory-Hu trees of unweighted graphs with polylogarithmically many max-flows](../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/almost-linear-flows-cuts-and-dynamic-matching/isolating-cuts-and-steiner-min-cuts/unweighted-gomory-hu-polylog-max-flows.md)
- [A near-maximum tree packing has many trees that 2-respect a minimum cut](../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/almost-linear-flows-cuts-and-dynamic-matching/deterministic-near-linear-minimum-cut/tree-packing-two-respects-minimum-cut.md)
- [Single-source minimum cut values](../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/almost-linear-flows-cuts-and-dynamic-matching/isolating-cuts-and-steiner-min-cuts/single-source-minimum-cut-values.md)

## Sources

- Amir Abboud, Robert Krauthgamer, Jason Li, Debmalya Panigrahi, Thatchaphol Saranurak, Ohad Trabelsi, "Breaking the Cubic Barrier for All-Pairs Max-Flow: Gomory-Hu Tree in Nearly Quadratic Time", FOCS (2022), arXiv:2111.04958.
