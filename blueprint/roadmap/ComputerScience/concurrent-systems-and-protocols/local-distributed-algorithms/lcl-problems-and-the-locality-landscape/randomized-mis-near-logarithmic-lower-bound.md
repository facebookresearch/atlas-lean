# Randomized MIS requires Omega(sqrt(log n / log log n)) rounds

Let $G = (V, E)$ be a simple connected graph with $n$ vertices and maximum degree $\Delta$, whose vertices carry distinct identifiers from $\{1, \dots, n^{O(1)}\}$. There are graphs (with unbounded degree) on which every possibly randomized LOCAL algorithm that always outputs a maximal independent set, only its running time depending on the randomness, has expected running time $\Omega\bigl(\sqrt{\log n / \log\log n}\bigr)$, and likewise $\Omega(\log\Delta / \log\log\Delta)$ as a function of $\Delta$; this holds even with identifiers $\{1, \dots, n\}$. For comparison, the randomized algorithms of Luby and of Alon, Babai and Itai use $O(\log n)$ rounds.

## Proof sketch

Cluster-tree graphs make two classes of vertices indistinguishable within $k$ rounds while an optimal vertex cover uses only the small class, so every $k$-round algorithm, even randomized, has large expected approximation ratio for minimum vertex cover. An always-correct maximal matching algorithm with expected time $T$ yields, by running it for $2T$ rounds and repairing locally, a vertex cover algorithm with fixed time $2T + 1$ and constant expected approximation ratio, which gives the bound for maximal matching in expectation. Maximal matching on a graph is MIS on its line graph, and rounds on the line graph are simulated with constant overhead, which transfers the bound to MIS.

## Depends on

- [The LOCAL model](../../distributed-execution-models/the-local-model.md)

## Sources

- F. Kuhn, T. Moscibroda, R. Wattenhofer, "Local Computation: Lower and Upper Bounds", Journal of the ACM 63(2) (2016), arXiv:1011.5470, Sections 4.3–4.4 (Theorems 22 and 23).
- N. Alon, L. Babai, A. Itai, "A fast and simple randomized parallel algorithm for the maximal independent set problem", Journal of Algorithms 7(4) (1986).
