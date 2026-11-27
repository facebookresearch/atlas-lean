# Randomized (Delta+1)-colouring in CONGEST in O(log^3 log n) rounds

Let $G = (V, E)$ be a simple connected graph with $n$ vertices and maximum degree $\Delta$, whose vertices carry distinct identifiers from $\{1, \dots, n^{O(1)}\}$. There is a randomized CONGEST algorithm that computes a $(\Delta + 1)$-colouring (and solves $(\deg+1)$-list colouring) with high probability in $O(\log^3 \log n)$ rounds.

## Proof sketch

Implement the sparse-dense decomposition and the synchronized colour trials of the LOCAL shattering algorithm with $O(\log n)$-bit messages: vertices try random colours from multi-trial sets encoded by short random seeds expanded by pseudorandom hashing, and almost-cliques are coordinated through low-congestion communication inside each clique. After shattering, the residual polylogarithmic-size components are coloured by the deterministic CONGEST list-colouring algorithm.

## Depends on

- [The (deg + 1)-list-coloring problem (D1LC)](../../../randomized-algorithms/sketching-streaming-and-sublinear-algorithms/palette-sparsification-and-sublinear-coloring/degree-plus-one-list-coloring.md)
- [The CONGEST model of distributed computing](../deterministic-network-decomposition/the-congest-model.md)

## Proof depends on

- [Randomized (Delta+1)-colouring in O(log* n) plus deterministic time on polylog-size instances](randomized-delta-plus-one-colouring-shattering.md)
- [Deterministic (Delta+1)-colouring in O(log^2 Delta log n) rounds without network decomposition](deterministic-delta-plus-one-colouring-log-squared.md)

## Sources

- M. M. Halldórsson, F. Kuhn, Y. Maus, T. Tonoyan, "Efficient Randomized Distributed Coloring in CONGEST", STOC 2021, arXiv:2012.14169.
