# Decremental (1+eps)-approximate single-source shortest paths

Let $G = (V, E, w)$ be a directed or undirected graph with $n$ vertices, $m$ edges and integer weights $w(e) \in [1, W]$, with a fixed source $s \in V$, undergoing an online sequence of edge deletions (or, in the vertex-decremental version, vertex deletions). For $\varepsilon > 0$, a *decremental $(1+\varepsilon)$-approximate SSSP* data structure maintains estimates $\tilde d(v)$ with

$$
\mathrm{dist}_G(s, v) \le \tilde d(v) \le (1 + \varepsilon)\,\mathrm{dist}_G(s, v) \quad \text{for all } v \in V \text{ reachable from } s \text{ in } G
$$

after every deletion, where $G$ is the current graph, and $\tilde d(v) = \infty$, meaning that $v$ is reported unreachable, for every other remaining vertex $v$. *Distance queries* return $\tilde d(v)$; *path queries* return, for $v$ reachable from $s$, an $s$-$v$ path in $G$ of length at most $(1+\varepsilon)\mathrm{dist}_G(s, v)$, and report that no path exists otherwise. Cost is the *total update time* over the whole deletion sequence, plus query time. Against an adaptive adversary, deletions may depend on all returned estimates and paths.

## Depends on

- [Dynamic graph problems](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/dynamic-graph-problems.md)
- [Oblivious and adaptive adversaries; amortized and worst-case update time](../../../data-structures/disjoint-sets-and-dynamic-trees/fully-dynamic-connectivity-and-spanning-forests/adversary-and-update-time-models.md)

## Sources

- Monika Henzinger, Sebastian Krinninger, Danupon Nanongkai, "Decremental Single-Source Shortest Paths on Undirected Graphs in Near-Linear Total Update Time", FOCS (2014); J. ACM 65(6) (2018), arXiv:1512.08148.
- Aaron Bernstein, Maximilian Probst Gutenberg, Thatchaphol Saranurak, "Deterministic Decremental SSSP and Approximate Min-Cost Flow in Almost-Linear Time", FOCS (2021), arXiv:2101.07149.
