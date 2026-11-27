# Deterministic O(sqrt n) worst-case dynamic minimum spanning forest via sparsification

Fully dynamic minimum spanning forest on an $n$-vertex graph with $m$ edges admits a deterministic data structure with $O(\sqrt{m})$ worst-case update time (Frederickson, using topology trees), and, by the sparsification technique of Eppstein, Galil, Italiano and Nissenzweig, a deterministic data structure with $O(\sqrt{n})$ worst-case update time. Until 2016 these were the best worst-case bounds for dynamic connectivity and MSF that hold against adaptive adversaries; the first improvement, by Kejlberg-Rasmussen, Kopelowitz, Pettie and Thorup (ESA 2016), to $O(\sqrt{n (\log\log n)^2/\log n})$ for connectivity, was subpolynomial, and the first polynomial improvements came in 2017.

## Proof sketch

Frederickson partitions a spanning tree into clusters of $\Theta(\sqrt{m})$ vertices and maintains, in two-dimensional topology trees, the lightest non-tree edge between every pair of clusters, so that after an update a replacement edge is found and the clusters are repaired in $O(\sqrt{m})$ time. Sparsification builds a balanced binary tree over a partition of the edges into groups of $n$ edges, maintains a sparse certificate (a spanning forest) at each node, and observes that an update changes $O(1)$ certificate edges per level, so the bound for $m = O(n)$ applies at each of $O(\log(m/n))$ levels with geometrically decreasing costs.

## Depends on

- [Fully dynamic connectivity, spanning forest and minimum spanning forest problems](fully-dynamic-connectivity-problems.md)
- [Oblivious and adaptive adversaries; amortized and worst-case update time](adversary-and-update-time-models.md)

## Proof depends on

- [Kruskal's algorithm gives a minimum spanning forest](../../../graph-algorithms/spanning-trees-flows-matchings/kruskal-s-algorithm/kruskal-minimal.md)

## Sources

- Greg N. Frederickson, "Data structures for on-line updating of minimum spanning trees, with applications", SIAM J. Comput. 14(4) (1985).
- David Eppstein, Zvi Galil, Giuseppe F. Italiano, Amnon Nissenzweig, "Sparsification - a technique for speeding up dynamic graph algorithms", J. ACM 44(5) (1997).
- Danupon Nanongkai, Thatchaphol Saranurak, "Dynamic Spanning Forest with Worst-Case Update Time: Adaptive, Las Vegas, and O(n^{1/2-epsilon})-Time", STOC (2017), arXiv:1611.03745.
