# Faster deterministic network decomposition in O(log^5 n) rounds

Let $G = (V, E)$ be a simple connected graph with $n$ vertices and maximum degree $\Delta$, whose vertices carry distinct identifiers from $\{1, \dots, n^{O(1)}\}$. There is a deterministic CONGEST algorithm, with $O(\log n)$-bit messages, that computes a network decomposition with $O(\log n)$ colours and weak diameter $O(\log^2 n)$ in $O(\log^5 n)$ rounds: each cluster $C$ comes with a Steiner tree of radius $O(\log^2 n)$ in $G$ whose terminals are exactly $C$ and which may use vertices outside $C$, and every vertex lies in $O(\log n)$ Steiner trees of each colour. In the LOCAL model this can be turned into a strong-diameter decomposition with $O(\log n)$ colours and strong diameter $O(\log n)$ in $O(\log^6 n)$ rounds. Moreover there is a deterministic CONGEST algorithm computing a network decomposition with $O(\log n)$ colours and strong diameter $O(\log n \cdot \log\log\log n)$ in $\tilde O(\log^3 n)$ rounds.

## Proof sketch

The first result repeats $O(\log n)$ times a deterministic ball-carving step that, in $O(\log^4 n)$ rounds, clusters at least half of the remaining vertices into non-adjacent clusters of weak diameter $O(\log^2 n)$. It refines the bit-by-bit clustering of Rozhoň and Ghaffari with a growth rule in which clusters grow only against the boundary they would absorb, and the analysis charges killed vertices to cluster growth across all phases simultaneously; communication inside a cluster runs over its Steiner tree, which is why only the weak diameter is bounded. The strong-diameter variant post-processes the weak-diameter decomposition in the LOCAL model. The second result develops randomized strong-diameter clustering procedures whose analysis uses only pairwise independence, which can be derandomized efficiently with the method of conditional expectations over small sample spaces; this yields decompositions with almost logarithmic parameters in both colours and strong diameter.

## Depends on

- [Network decomposition with weak or strong diameter](network-decomposition-weak-strong-diameter.md)
- [The CONGEST model of distributed computing](the-congest-model.md)

## Proof depends on

- [Polylogarithmic-time deterministic network decomposition](polylogarithmic-deterministic-network-decomposition.md)

## Sources

- M. Ghaffari, C. Grunau, V. Rozhoň, "Improved Deterministic Network Decomposition", SODA 2021, arXiv:2007.08253, Theorems 1.1, 2.1 and 2.2.
- M. Ghaffari, C. Grunau, B. Haeupler, S. Ilchi, V. Rozhoň, "Improved Distributed Network Decomposition, Hitting Sets, and Spanners, via Derandomization", SODA 2023, arXiv:2209.11669, Theorem 1.1.
