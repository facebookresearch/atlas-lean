# Subpolynomial deterministic network decomposition before polylogarithmic time

Let $G = (V, E)$ be a simple connected graph with $n$ vertices and maximum degree $\Delta$, whose vertices carry distinct identifiers from $\{1, \dots, n^{O(1)}\}$. There is a deterministic LOCAL algorithm computing a $(2^{O(\sqrt{\log n})}, 2^{O(\sqrt{\log n})})$-network decomposition in $2^{O(\sqrt{\log n})}$ rounds. Consequently maximal independent set and $(\Delta+1)$-colouring have deterministic LOCAL algorithms with $2^{O(\sqrt{\log n})}$ rounds.

## Proof sketch

Recursively cluster the graph: compute a ruling set of the current cluster graph, grow clusters around rulers, and contract; balancing the number of recursion levels against the growth in diameter and colours per level at $\sqrt{\log n}$ gives the stated bound. The consequences follow by the conversion lemma since greedy MIS and colouring have SLOCAL locality one.

## Depends on

- [Network decomposition with weak or strong diameter](network-decomposition-weak-strong-diameter.md)
- [The LOCAL model](../../distributed-execution-models/the-local-model.md)

## Proof depends on

- [Network decompositions convert sequential local algorithms into LOCAL algorithms](slocal-to-local-via-network-decomposition.md)

## Sources

- A. Panconesi, A. Srinivasan, "On the Complexity of Distributed Network Decomposition", Journal of Algorithms 20(2) (1996).
- B. Awerbuch, A. V. Goldberg, M. Luby, S. A. Plotkin, "Network decomposition and locality in distributed computation", FOCS 1989.
