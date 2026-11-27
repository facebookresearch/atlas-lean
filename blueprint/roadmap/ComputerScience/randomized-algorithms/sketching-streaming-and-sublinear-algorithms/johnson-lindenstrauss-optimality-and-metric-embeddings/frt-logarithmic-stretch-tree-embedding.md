# Fakcharoenphol-Rao-Talwar O(log n) expected-stretch tree embeddings

Every $n$-point metric space admits a probabilistic embedding into dominating tree metrics with expected stretch $O(\log n)$; the trees are hierarchically well-separated, and a tree from the distribution can be sampled in randomized polynomial time. This is existentially tight: there are $n$-point metrics (for instance shortest-path metrics of constant-degree expanders) for which every such distribution has expected stretch $\Omega(\log n)$. It improves Bartal's bounds $O(\log^2 n)$ (1996) and $O(\log n\log\log n)$ (1998).

## Proof sketch

Scale so that distances lie in $[1, 2^{\delta}]$, pick a uniformly random permutation of the points and a uniform $\beta \in [1, 2]$, and build a hierarchical partition: at level $i$, every current cluster is split by assigning each point to the first center in the permutation within distance $\beta 2^{i-1}$. The tree has the clusters as nodes and edges of length $2^{i}$ at level $i$, so it dominates $d$. A pair $x, y$ is separated at level $i$ only if some center $w$ settles exactly one of them; the probability that $w$, the $s$-th closest point to $x$, does so is at most $O(d(x, y)/2^{i})\cdot\frac{1}{s}$, and summing $2^{i}$ times these probabilities over levels and centers gives $O(\log n)\, d(x, y)$.

## Depends on

- [Probabilistic embedding of a metric into dominating tree metrics](probabilistic-embeddings-into-dominating-trees.md)
- [Tree metric](../../../../GraphTheory/graph-families-and-operations/tree-metrics-and-the-four-point-condition/is-tree-metric.md)
- [Hierarchically separated trees](../../../online-algorithms/metrical-task-systems-and-hst-embeddings/hierarchically-separated-tree.md)

## Sources

- Jittat Fakcharoenphol, Satish Rao, Kunal Talwar, "A tight bound on approximating arbitrary metrics by tree metrics", STOC (2003); J. Comput. Syst. Sci. 69 (2004).
- Yair Bartal, "Probabilistic approximation of metric spaces and its algorithmic applications", FOCS (1996).
- Yair Bartal, "On approximating arbitrary metrics by tree metrics", STOC (1998).
