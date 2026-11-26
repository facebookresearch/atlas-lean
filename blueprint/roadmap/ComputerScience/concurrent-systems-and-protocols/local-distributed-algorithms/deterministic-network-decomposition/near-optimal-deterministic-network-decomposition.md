# Near-optimal deterministic network decomposition in $\tilde O(\log^2 n)$ rounds

Let $G = (V, E)$ be a simple connected graph with $n$ vertices and maximum degree $\Delta$, whose vertices carry distinct identifiers from $\{1, \dots, n^{O(1)}\}$. There is a deterministic distributed algorithm that computes a network decomposition with $O(\log n)$ colours and diameter $O(\log n)$ in $\tilde O(\log^2 n)$ rounds, where $\tilde O$ hides factors polynomial in $\log\log n$. This is near-optimal for decompositions used in the standard way, since processing a decomposition with $C$ colours and diameter $D$ costs $\Theta(C \cdot D)$ rounds, and, as Ghaffari and Grunau note, $C \cdot D = \tilde\Omega(\log^2 n)$ even for an ideal decomposition. The same work gives a deterministic algorithm for maximal independent set in $\tilde O(\log^{5/3} n)$ rounds.

## Proof sketch

Rather than building colour classes independently, build all colours together through a sequence of low-diameter clusterings at geometrically increasing scales, using a deterministic ruling-set primitive computed in near-optimal time as the core subroutine. Careful accounting shows that each scale contributes $\tilde O(\log n)$ rounds while the number of scales is $O(\log n)$ only in the worst case, amortized over the decreasing remaining vertex set, giving $\tilde O(\log^2 n)$ overall. The MIS result combines the decomposition with a faster randomized-to-deterministic shattering step.

## Depends on

- [Network decomposition with weak or strong diameter](network-decomposition-weak-strong-diameter.md)

## Proof depends on

- [Faster deterministic network decomposition in O(log^5 n) rounds](faster-deterministic-network-decomposition.md)

## Sources

- M. Ghaffari, C. Grunau, "Near-Optimal Deterministic Network Decomposition and Ruling Set, and Improved MIS", FOCS 2024, arXiv:2410.19516.
