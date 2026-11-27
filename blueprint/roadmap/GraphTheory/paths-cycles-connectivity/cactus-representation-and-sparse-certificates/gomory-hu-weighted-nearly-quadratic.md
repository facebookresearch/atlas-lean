# Gomory-Hu trees of weighted graphs in nearly quadratic time

There is a randomized (Monte Carlo) algorithm that, given an undirected graph with $n$ vertices and positive integer edge weights bounded by $n^{O(1)}$, computes a cut-equivalent tree in $\tilde O(n^2)$ time with probability $1 - n^{-c}$. This is the first subcubic algorithm for all-pairs max-flow in general weighted graphs; under the hypothesis that all-pairs shortest paths requires $n^{3 - o(1)}$ time, it separates all-pairs max-flow from all-pairs shortest paths.

## Proof sketch

Following Gomory and Hu and the single-source reduction of Abboud, Krauthgamer and Trabelsi, the construction reduces, via max-flow calls on contracted graphs of total size $\tilde O(m)$, to single-source terminal mincuts: for a terminal set $U$ and source $s \in U$ whose values $\lambda(s,t)$, $t \in U \setminus \{s\}$, are within a factor $1.1$ of the Steiner connectivity $\lambda(U)$, compute all these values. The new ingredient is a set of $O(\log n)$ guide trees: $U$-Steiner trees such that each $t$ has an $(s,t)$-mincut $4$-respected by one of them. They exist because a graph packs $\lambda(U)/2$ edge-disjoint $U$-Steiner trees (Mader splitting-off with Nash-Williams-Tutte), and are found by packing Steiner trees with multiplicative weights and Mehlhorn's $2$-approximation on a $(1+\epsilon)$-cut sparsifier, in $\tilde O(n^2)$ time; isolating cuts along the guide trees then give the single-source values with polylogarithmically many max-flow calls.

## Depends on

- [Flow-equivalent and cut-equivalent trees of weighted graphs](flow-equivalent-and-cut-equivalent-trees.md)

## Proof depends on

- [Isolating cut lemma with logarithmically many max-flow calls](../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/almost-linear-flows-cuts-and-dynamic-matching/isolating-cuts-and-steiner-min-cuts/isolating-cut-lemma.md)
- [Gomory-Hu trees of unweighted graphs with polylogarithmically many max-flows](../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/almost-linear-flows-cuts-and-dynamic-matching/isolating-cuts-and-steiner-min-cuts/unweighted-gomory-hu-polylog-max-flows.md)
- [Single-source minimum cut values](../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/almost-linear-flows-cuts-and-dynamic-matching/isolating-cuts-and-steiner-min-cuts/single-source-minimum-cut-values.md)

## Sources

- Amir Abboud, Robert Krauthgamer, Jason Li, Debmalya Panigrahi, Thatchaphol Saranurak, Ohad Trabelsi, "Breaking the Cubic Barrier for All-Pairs Max-Flow: Gomory-Hu Tree in Nearly Quadratic Time", FOCS (2022), arXiv:2111.04958.
