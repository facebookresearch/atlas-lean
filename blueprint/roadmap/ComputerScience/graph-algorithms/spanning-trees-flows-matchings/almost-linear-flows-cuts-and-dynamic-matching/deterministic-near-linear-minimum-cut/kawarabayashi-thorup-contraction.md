# Kawarabayashi-Thorup contraction to O(m/delta) edges preserving non-trivial minimum cuts

Let $G$ be a simple connected undirected graph with $n$ vertices, $m$ edges and minimum degree $\delta$. There is a deterministic $\tilde O(m)$-time algorithm that computes a partition $\mathcal{Q}$ of $V$ preserving all non-trivial minimum cuts such that $G / \mathcal{Q}$ has $\tilde O(m / \delta)$ edges and $\tilde O(n/\delta)$ vertices. Moreover (Lo-Schmidt-Thorup) such a partition exists with $G / \mathcal{Q}$ having $O(n/\delta)$ vertices and $O(n)$ edges and can be computed in $\tilde O(m)$ time; consequently every simple graph has $O((n/\delta)^2)$ non-trivial minimum cuts.

## Proof sketch

A side $S$ of a non-trivial cut with $|\partial S| \le \delta$ has $|S| \ge \delta$, since $2 \le |S| \le \delta - 1$ forces $|\partial S| \ge |S|(\delta - |S| + 1) \ge 2\delta - 2$; so non-trivial minimum cuts have both sides of volume at least $\delta^2$. Decompose $G$ into clusters of high conductance with few inter-cluster edges; a cut of value at most $\delta$ can cut a high-conductance cluster only in a small set, and trimming low-degree-into-cluster vertices and shaving vertices with at most half their neighbors inside makes the remaining cluster cores lie entirely on one side of every non-trivial minimum cut. Contracting the cores leaves $\tilde O(m/\delta)$ edges; the Lo-Schmidt-Thorup refinement removes the logarithmic losses, and applying Karger's counting bound to the contracted graph gives the $O((n/\delta)^2)$ count.

## Depends on

- [Contractions preserving all non-trivial minimum cuts of a simple graph](nontrivial-mincut-preserving-contraction.md)

## Proof depends on

- [At most $n(n-1)/2$ minimum cuts](../../../../randomized-algorithms/karger-s-algorithm/two-mul-length-min-cuts-le.md)
- [Volume of a vertex set](../../../../../GraphTheory/algebraic-graph-theory/part-02/conductance-and-cheeger-s-inequality/volume.md)

## Sources

- Ken-ichi Kawarabayashi, Mikkel Thorup, "Deterministic Edge Connectivity in Near-Linear Time", STOC (2015) and Journal of the ACM (2019), arXiv:1411.5123.
- On-Hei Solomon Lo, Jens M. Schmidt, Mikkel Thorup, "Compact Cactus Representations of all Non-Trivial Min-Cuts", Discrete Applied Mathematics (2020), arXiv:1810.03865.
- Monika Henzinger, Satish Rao, Di Wang, "Local Flow Partitioning for Faster Edge Connectivity", SODA (2017) and SIAM Journal on Computing (2020), arXiv:1704.01254.
