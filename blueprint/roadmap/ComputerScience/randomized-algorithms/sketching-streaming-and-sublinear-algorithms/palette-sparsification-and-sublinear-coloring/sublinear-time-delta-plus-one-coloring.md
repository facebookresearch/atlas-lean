# Sublinear-time (Delta + 1)-coloring with Theta-tilde(n^{3/2}) queries

Let an $n$-vertex graph of maximum degree $\Delta$ be accessible through degree queries, neighbor queries (the $i$-th neighbor of $v$) and pair queries (whether $\{u, v\} \in E$).

1. There is a randomized algorithm that outputs a proper $(\Delta + 1)$-coloring with high probability in $O(n\sqrt{n}\,\log^{c} n)$ time for an absolute constant $c$.
2. For every constant $c > 1$, every randomized algorithm that outputs a proper $(c\Delta)$-coloring, in particular a proper $(\Delta + 1)$-coloring, with probability at least a sufficiently large constant makes $\Omega(n\sqrt{n})$ queries on some input.

## Proof sketch

If $\Delta \le \sqrt{n}$, read the whole graph with $O(n\Delta) = O(n\sqrt{n})$ neighbor queries and color greedily. Otherwise sample lists of $k = O(\log n)$ colors; for each color $c$ the set $S_c$ of vertices that sampled $c$ has expected size $nk/(\Delta + 1)$, and pair queries inside every $S_c$ reveal the conflict graph using about $\sum_c |S_c|^2 = O(n^2 k^2/\Delta) = O(n\sqrt{n}\log^2 n)$ queries; the palette sparsification theorem then supplies the coloring. The lower bound uses Yao's principle on graphs of maximum degree $\sqrt{n} + 1$ built from $\sqrt{n}$ complete bipartite blocks plus a hidden uniformly random perfect matching on one part: an algorithm told everything except the matching finds only $o(n)$ of its edges with $o(n\sqrt{n})$ queries, and then every coloring it commits to is improper on some matching edge with constant probability.

## Proof depends on

- [Assadi-Chen-Khanna palette sparsification theorem for (Delta + 1)-coloring](palette-sparsification-theorem-delta-plus-one.md)
- [The conflict graph of palette sparsification has O(n log^2 n) edges](conflict-graph-has-quasilinear-size.md)
- [Yao's minimax principle](../../../../TheoryOfComputation/randomized-and-quantum-complexity/yao-s-minimax-principle/yao-minimax.md)

## Sources

- Sepehr Assadi, Yu Chen, Sanjeev Khanna, "Sublinear Algorithms for (Delta + 1) Vertex Coloring", SODA (2019), arXiv:1807.08886.
