# Randomized MIS requires Omega(sqrt(log n / log log n)) rounds

Let $G = (V, E)$ be a simple connected graph with $n$ vertices and maximum degree $\Delta$, whose vertices carry distinct identifiers from $\{1, \dots, n^{O(1)}\}$. Every randomized LOCAL algorithm that computes a maximal independent set with probability at least $1/2$ on every $n$-vertex graph uses $\Omega\bigl(\sqrt{\log n / \log\log n}\bigr)$ rounds on some graph (with unbounded degree). For comparison, the randomized algorithms of Luby and of Alon, Babai and Itai use $O(\log n)$ rounds.

## Proof sketch

The bound constructs graphs that are locally tree-like and indistinguishable within $t$ rounds while their independence structure differs, using cluster-tree constructions.

## Depends on

- [The LOCAL model](../../distributed-execution-models/the-local-model.md)

## Sources

- F. Kuhn, T. Moscibroda, R. Wattenhofer, "Local Computation: Lower and Upper Bounds", Journal of the ACM 63(2) (2016).
- N. Alon, L. Babai, A. Itai, "A fast and simple randomized parallel algorithm for the maximal independent set problem", Journal of Algorithms 7(4) (1986).
