# Ball carving: every graph has an (O(log n), O(log n)) strong-diameter decomposition

Let $G = (V, E)$ be a simple connected graph with $n$ vertices and maximum degree $\Delta$, whose vertices carry distinct identifiers from $\{1, \dots, n^{O(1)}\}$. There exists a $(C, D)$-network decomposition of $G$ with strong diameter, where $C = O(\log n)$ and $D = O(\log n)$. Moreover such a strong-diameter decomposition can be computed by a randomized LOCAL algorithm in $O(\log^2 n)$ rounds with high probability (Elkin–Neiman). The earlier randomized $O(\log^2 n)$-round algorithm of Linial and Saks guarantees only weak diameter $O(\log n)$.

## Proof sketch

Existence is a sequential argument. Build one colour class at a time on the remaining graph. For a remaining vertex $v$, grow balls $B(v, r)$ in the remaining graph for $r = 0, 1, 2, \dots$ until $\lvert B(v, r+1) \rvert \le 2 \lvert B(v, r) \rvert$; this happens for some $r = O(\log n)$, since otherwise the ball would double more than $\log_2 n$ times. Take $B(v, r)$ as a cluster of strong diameter at most $2r$ and remove the boundary $B(v, r+1) \setminus B(v, r)$ from the current colour class, so that clusters of one colour are non-adjacent; the boundary has at most as many vertices as the cluster, so each colour covers at least half of the vertices remaining at its start, and $O(\log n)$ colours suffice. The randomized distributed construction of Elkin and Neiman carves $O(\log n)$ blocks in sequence; in each block every remaining vertex $v$ draws an independent exponential radius $r_v$ and broadcasts it to distance $\lfloor r_v \rfloor$, and a vertex joins the block, in the cluster of the centre maximizing $r_v - \mathrm{dist}(\cdot, v)$, only if this maximum exceeds the second largest value by more than $1$. Every vertex on a shortest path from a centre to a vertex that chose it chooses the same centre, which bounds the strong diameter by $O(\log n)$ when all radii are $O(\log n)$, and with $\Theta(\log n)$ blocks every vertex is carved with high probability.

## Depends on

- [Network decomposition with weak or strong diameter](network-decomposition-weak-strong-diameter.md)
- [The LOCAL model](../../distributed-execution-models/the-local-model.md)

## Sources

- N. Linial, M. Saks, "Low diameter graph decompositions", Combinatorica 13(4) (1993).
- M. Elkin, O. Neiman, "Distributed Strong Diameter Network Decomposition", PODC 2016, arXiv:1602.05437, abstract and Theorem 1.
