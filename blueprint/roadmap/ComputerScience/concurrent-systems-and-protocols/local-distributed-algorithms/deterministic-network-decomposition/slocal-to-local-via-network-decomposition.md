# Network decompositions convert sequential local algorithms into LOCAL algorithms

Let $G = (V, E)$ be a simple connected graph with $n$ vertices and maximum degree $\Delta$, whose vertices carry distinct identifiers from $\{1, \dots, n^{O(1)}\}$. Suppose a problem has an SLOCAL algorithm with locality $r$, and a $(C, D)$-network decomposition of the power graph $G^{r}$ with weak diameter $D$ (measured in $G^{r}$) is given. Then the problem can be solved deterministically in the LOCAL model in $O\bigl(C \cdot (D + 1) \cdot r\bigr)$ rounds.

## Proof sketch

Process the colour classes one after another. Within a colour class, clusters are at distance greater than $r$ in $G$, so they can simulate the sequential algorithm independently and in parallel: a leader of each cluster gathers the radius-$r$ neighbourhood of the whole cluster in $O(D r)$ rounds, runs the SLOCAL algorithm on the cluster's vertices in an arbitrary order, and broadcasts the results. Since no two simultaneously processed vertices from different clusters can see each other's writes, the parallel execution is consistent with some sequential order.

## Depends on

- [The SLOCAL model and its polylogarithmic class](the-slocal-model.md)
- [Network decomposition with weak or strong diameter](network-decomposition-weak-strong-diameter.md)
- [The LOCAL model](../../distributed-execution-models/the-local-model.md)

## Sources

- M. Ghaffari, F. Kuhn, Y. Maus, "On the Complexity of Local Distributed Graph Problems", STOC 2017, arXiv:1611.02663.
- B. Awerbuch, A. V. Goldberg, M. Luby, S. A. Plotkin, "Network decomposition and locality in distributed computation", FOCS 1989.
