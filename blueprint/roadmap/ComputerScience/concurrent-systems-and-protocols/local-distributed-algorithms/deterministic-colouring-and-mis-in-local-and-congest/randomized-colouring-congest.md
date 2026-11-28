# Randomized (Delta+1)-list colouring in CONGEST in O(log^5 log n) rounds

Let $G = (V, E)$ be a simple connected graph with $n$ vertices and maximum degree $\Delta$, whose vertices carry distinct identifiers from $\{1, \dots, n^{O(1)}\}$. Suppose every vertex $v$ has a list $\Psi(v) \subseteq \{1, \dots, U\}$ of exactly $\Delta + 1$ colours, where $U = \mathrm{poly}(n)$. There is a randomized CONGEST algorithm that with high probability computes a proper colouring in which every vertex receives a colour from its list in $O(\log^5 \log n)$ rounds; in particular this solves $(\Delta + 1)$-colouring. Its subroutine for the residual low-degree instances solves $(\deg+1)$-list colouring on graphs of maximum degree $\Delta_0$ in $O(\log \Delta_0 + \log^5 \log n)$ rounds with high probability.

## Proof sketch

Compute an almost-clique decomposition into sparse vertices and dense almost-cliques in $O(1)$ rounds and generate slack by one round of random colour trials. Sparse vertices are coloured by repeated random colour trials, with multiple trials encoded in single $O(\log n)$-bit messages; each almost-clique builds an overlay simulating all-to-all communication inside it in $O(\log\log n)$ rounds and coordinates synchronized colour trials through a leader. Once the uncoloured degree is $\Delta_0 = \mathrm{poly}\log n$, the remaining problem is a $(\deg+1)$-list colouring instance. It is solved by the shattering framework: $O(\log \Delta_0)$ iterations of random colour trials leave components of size $N = \mathrm{poly}\log n$. Each component is split by a deterministic network decomposition into clusters of diameter $\mathrm{poly}\log\log n$. Each cluster maps its colours into a space of size $\mathrm{poly}(N)$ and runs $O(\log n)$ independent instances of random colour trials in parallel for $O(\log N)$ iterations, agreeing on a successful one over the small diameter. The network decomposition is the bottleneck, giving $O(\log^5 \log n)$ rounds.

## Depends on

- [The (deg + 1)-list-coloring problem (D1LC)](../../../randomized-algorithms/sketching-streaming-and-sublinear-algorithms/palette-sparsification-and-sublinear-coloring/degree-plus-one-list-coloring.md)
- [The CONGEST model of distributed computing](../deterministic-network-decomposition/the-congest-model.md)

## Proof depends on

- [Graph shattering after a randomized pre-shattering phase](graph-shattering-lemma.md)
- [Faster deterministic network decomposition in O(log^5 n) rounds](../deterministic-network-decomposition/faster-deterministic-network-decomposition.md)

## Sources

- M. M. Halldórsson, F. Kuhn, Y. Maus, T. Tonoyan, "Efficient Randomized Distributed Coloring in CONGEST", STOC 2021, arXiv:2012.14169, Theorems 1.1 and 10.1 and Section 2.
