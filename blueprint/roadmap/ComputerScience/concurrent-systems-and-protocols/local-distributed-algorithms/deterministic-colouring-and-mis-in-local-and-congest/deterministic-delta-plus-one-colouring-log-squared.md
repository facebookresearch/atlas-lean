# Deterministic (Delta+1)-colouring in O(log^2 Delta log n) rounds without network decomposition

Let $G = (V, E)$ be a simple connected graph with $n$ vertices and maximum degree $\Delta$, whose vertices carry distinct identifiers from $\{1, \dots, n^{O(1)}\}$. There is a deterministic algorithm that solves every $(\deg+1)$-list colouring instance, and in particular $(\Delta + 1)$-colouring, in $O(\log^2 \Delta \cdot \log n)$ rounds of the CONGEST model. The algorithm does not use network decompositions.

## Proof sketch

Colour a constant fraction of the remaining vertices per phase, so $O(\log n)$ phases suffice. Within a phase, each uncoloured vertex chooses a colour from its list by fixing the bits of the colour one at a time ($O(\log \Delta)$ bit levels after a list-shrinking step): at each level vertices decide a bit so as to keep a pessimistic estimator of the number of conflicts small, derandomizing a random choice by a locally computable weighted defective splitting, which itself costs $O(\log \Delta)$ rounds per level. A constant fraction of vertices ends with conflict-free colours.

## Depends on

- [The (deg + 1)-list-coloring problem (D1LC)](../../../randomized-algorithms/sketching-streaming-and-sublinear-algorithms/palette-sparsification-and-sublinear-coloring/degree-plus-one-list-coloring.md)
- [The CONGEST model of distributed computing](../deterministic-network-decomposition/the-congest-model.md)

## Sources

- M. Ghaffari, F. Kuhn, "Deterministic Distributed Vertex Coloring: Simpler, Faster, and without Network Decomposition", FOCS 2021, arXiv:2011.04511.
