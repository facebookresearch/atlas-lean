# Nanongkai-Saranurak: adaptive Las Vegas dynamic spanning forest in O(n^0.49306) worst-case time

There are randomized algorithms maintaining a spanning forest of an $n$-vertex graph under edge insertions and deletions against an adaptive adversary, with

1. a Monte Carlo algorithm with $O(n^{0.4 + o(1)})$ worst-case update time, where the $o(1)$ hides an $O(\sqrt{\log \log n / \log n})$ term;
2. a Las Vegas algorithm with $O(n^{0.49306})$ worst-case update time with high probability.

These are the first polynomial improvements over the deterministic $O(\sqrt{n})$ worst-case bound for algorithms that work against an adaptive adversary.

## Proof sketch

The graph is decomposed into expanders plus few inter-cluster edges. Inside an expander, a tree-edge deletion has a replacement edge that can be found by local exploration from the smaller side, whose volume is small by expansion. Deletions are handled by decrementally pruning low-conductance cuts out of each expander, and the inter-cluster edges, which are few, are handled recursively on a contracted graph; balancing these two parts gives the polynomial savings.

## Depends on

- [Oblivious and adaptive adversaries; amortized and worst-case update time](adversary-and-update-time-models.md)
- [Fully dynamic connectivity, spanning forest and minimum spanning forest problems](fully-dynamic-connectivity-problems.md)

## Proof depends on

- [(phi, epsilon)-expander decompositions of an undirected graph](../../../../GraphTheory/graph-families-and-operations/expander-decomposition-and-pruning/phi-epsilon-expander-decomposition.md)
- [Replacement edges after deleting a spanning-forest edge](replacement-edge-lemma.md)

## Sources

- Danupon Nanongkai, Thatchaphol Saranurak, "Dynamic Spanning Forest with Worst-Case Update Time: Adaptive, Las Vegas, and O(n^{1/2-epsilon})-Time", STOC (2017), arXiv:1611.03745.
- Christian Wulff-Nilsen, "Fully-Dynamic Minimum Spanning Forest with Improved Worst-Case Update Time", STOC (2017), arXiv:1611.02864.
