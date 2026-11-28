# Holm-de Lichtenberg-Thorup: deterministic polylogarithmic amortized connectivity and MSF

There are deterministic data structures on $n$ vertices, starting from the empty graph, with the following amortized costs:

1. fully dynamic connectivity with $O(\log^2 n)$ amortized time per update and $O(\log n / \log \log n)$ worst-case time per query;
2. fully dynamic minimum spanning forest with $O(\log^4 n)$ amortized time per update.

Being deterministic, both bounds hold against adaptive adversaries.

## Proof sketch

Each edge carries a level $\ell(e) \in \{0, \dots, \lfloor \log_2 n \rfloor\}$ that only increases, and $F_i$ denotes the forest of tree edges of level at least $i$. Two invariants are kept: $F$ is a maximum spanning forest with respect to the levels, and every tree of $F_i$ has at most $n/2^i$ vertices. When a tree edge of level $i$ is deleted, the search for a replacement scans level-$i$ non-tree edges from the smaller side and raises the level of every unsuccessful candidate and of the smaller side's tree edges, which preserves the size invariant. Each level increase is paid by Euler-tour-tree operations of cost $O(\log n)$, and an edge rises at most $\log_2 n$ times, giving $O(\log^2 n)$ amortized.

## Depends on

- [Oblivious and adaptive adversaries; amortized and worst-case update time](adversary-and-update-time-models.md)
- [Fully dynamic connectivity, spanning forest and minimum spanning forest problems](fully-dynamic-connectivity-problems.md)

## Proof depends on

- [Euler tour](../euler-tour-tree/tour.md)
- [Amortized cost of an operation](../../amortized-analysis/amortized-cost.md)
- [Kruskal's algorithm gives a minimum spanning forest](../../../graph-algorithms/spanning-trees-flows-matchings/kruskal-s-algorithm/kruskal-minimal.md)
- [Replacement edges after deleting a spanning-forest edge](replacement-edge-lemma.md)

## Sources

- Jacob Holm, Kristian de Lichtenberg, Mikkel Thorup, "Poly-logarithmic deterministic fully-dynamic algorithms for connectivity, minimum spanning tree, 2-edge, and biconnectivity", J. ACM 48(4) (2001).
- Monika R. Henzinger, Valerie King, "Randomized fully dynamic graph algorithms with polylogarithmic time per operation", J. ACM 46(4) (1999).
- Christian Wulff-Nilsen, "Faster Deterministic Fully-Dynamic Graph Connectivity", SODA (2013), arXiv:1209.5608.
