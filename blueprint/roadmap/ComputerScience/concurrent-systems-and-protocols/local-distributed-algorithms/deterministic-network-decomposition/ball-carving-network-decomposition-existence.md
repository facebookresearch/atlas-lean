# Ball carving: every graph has an (O(log n), O(log n)) strong-diameter decomposition

Let $G = (V, E)$ be a simple connected graph with $n$ vertices and maximum degree $\Delta$, whose vertices carry distinct identifiers from $\{1, \dots, n^{O(1)}\}$. There exists a $(C, D)$-network decomposition of $G$ with strong diameter, where $C = O(\log n)$ and $D = O(\log n)$. Moreover such a decomposition can be computed by a randomized LOCAL algorithm in $O(\log^2 n)$ rounds with high probability.

## Proof sketch

Build one colour class at a time on the remaining graph. For a vertex $v$, grow balls $B(v, r)$ for $r = 0, 1, 2, \dots$ until $\lvert B(v, r+1) \rvert \le 2 \lvert B(v, r) \rvert$; this happens for some $r = O(\log n)$. Take $B(v, r)$ as a cluster and delete $B(v, r+1)$ from the current colour class, so that clusters of one colour are non-adjacent; since each step removes at most as many boundary vertices as cluster vertices, each colour covers at least half of the remaining vertices, and $O(\log n)$ colours suffice. The randomized distributed version uses random exponential shifts to grow balls in parallel.

## Depends on

- [Network decomposition with weak or strong diameter](network-decomposition-weak-strong-diameter.md)
- [The LOCAL model](../../distributed-execution-models/the-local-model.md)

## Sources

- N. Linial, M. Saks, "Low diameter graph decompositions", Combinatorica 13(4) (1993).
