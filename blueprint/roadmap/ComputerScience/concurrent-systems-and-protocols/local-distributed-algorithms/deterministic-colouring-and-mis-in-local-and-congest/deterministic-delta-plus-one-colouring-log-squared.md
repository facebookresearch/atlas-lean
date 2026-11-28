# Deterministic (Delta+1)-colouring in O(log^2 Delta log n) rounds without network decomposition

Let $G = (V, E)$ be a simple connected graph with $n$ vertices and maximum degree $\Delta$, whose vertices carry distinct identifiers from $\{1, \dots, n^{O(1)}\}$. There is a deterministic algorithm that computes a proper $(\Delta + 1)$-colouring in $O(\log^2 \Delta \cdot \log n)$ rounds of the CONGEST model, with $O(\log n)$-bit messages. More generally, consider $(\deg+1)$-list colouring with lists $L_v \subseteq \{1, \dots, C\}$ and $\lvert L_v \rvert \ge \deg(v) + 1$. It can be solved deterministically in $O(\log^2 \Delta \cdot \log n)$ rounds with $O(\Delta \log C)$-bit messages, or in $O(\log^2 C \cdot \log n)$ rounds with $O(\log C)$-bit messages; the latter is a CONGEST bound of $O(\log^2 \Delta \cdot \log n)$ rounds when $C = \mathrm{poly}(\Delta)$, but not for an arbitrary palette polynomial in $n$. The algorithms do not use network decompositions.

## Proof sketch

Colour a constant fraction of the remaining vertices per phase, so $O(\log n)$ phases suffice. A uniformly random colour choice from each list gives fewer than $n$ monochromatic edges in expectation, and from any assignment with $O(n)$ monochromatic edges a properly coloured set of $\Theta(n)$ vertices is extracted. The phase derandomizes this choice by gradual rounding: start from a $1/\Theta(\deg(v))$-integral fractional colour assignment, whose expected number of monochromatic edges is the cost, and repeatedly round $1/(2Q)$-integral values to $1/Q$-integral ones. A weighted defective colouring with $O(1/\varepsilon)$ colours, whose monochromatic edges carry at most an $\varepsilon$ fraction of the edge weight (the probability of becoming monochromatic), lets the colour classes round in turn in $O(1/\varepsilon)$ rounds, losing a factor $1 + O(\varepsilon)$ in cost. With $\varepsilon = 1/\log\Delta$ the $O(\log\Delta)$ rounding steps take $O(\log^2 \Delta)$ rounds and lose only a constant factor. In CONGEST with small messages, the vertices instead round a choice among parts of a fixed partition of the colour space $\{1, \dots, C\}$, restricting their lists, so the bit-length of a colour enters the round complexity as $\log^2 C$.

## Depends on

- [The (deg + 1)-list-coloring problem (D1LC)](../../../randomized-algorithms/sketching-streaming-and-sublinear-algorithms/palette-sparsification-and-sublinear-coloring/degree-plus-one-list-coloring.md)
- [The CONGEST model of distributed computing](../deterministic-network-decomposition/the-congest-model.md)

## Sources

- M. Ghaffari, F. Kuhn, "Deterministic Distributed Vertex Coloring: Simpler, Faster, and without Network Decomposition", FOCS 2021, arXiv:2011.04511, Theorem 1.1 and Section 1.3.
