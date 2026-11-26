# Faster deterministic network decomposition in O(log^5 n) rounds

Let $G = (V, E)$ be a simple connected graph with $n$ vertices and maximum degree $\Delta$, whose vertices carry distinct identifiers from $\{1, \dots, n^{O(1)}\}$. There is a deterministic CONGEST algorithm, with $O(\log n)$-bit messages, that computes a network decomposition with $O(\log n)$ colours and polylogarithmic strong diameter in $O(\log^5 n)$ rounds. Moreover there is a deterministic algorithm computing a network decomposition with $O(\log n)$ colours and strong diameter $O(\log n \cdot \log\log\log n)$ in $\tilde O(\log^3 n)$ rounds.

## Proof sketch

The first result refines the bit-by-bit clustering with a cleverer growth rule in which clusters grow only against the boundary they would absorb and the analysis charges killed vertices to cluster growth across all phases simultaneously. The second develops randomized clustering procedures whose analysis uses only pairwise independence, which can be derandomized efficiently with the method of conditional expectations over small sample spaces; this yields decompositions with almost logarithmic parameters in both colours and diameter.

## Depends on

- [Network decomposition with weak or strong diameter](network-decomposition-weak-strong-diameter.md)
- [The CONGEST model of distributed computing](the-congest-model.md)

## Proof depends on

- [Polylogarithmic-time deterministic network decomposition](polylogarithmic-deterministic-network-decomposition.md)

## Sources

- M. Ghaffari, C. Grunau, V. Rozhoň, "Improved Deterministic Network Decomposition", SODA 2021, arXiv:2007.08253.
- M. Ghaffari, C. Grunau, B. Haeupler, S. Ilchi, V. Rozhoň, "Improved Distributed Network Decomposition, Hitting Sets, and Spanners, via Derandomization", SODA 2023, arXiv:2209.11669.
