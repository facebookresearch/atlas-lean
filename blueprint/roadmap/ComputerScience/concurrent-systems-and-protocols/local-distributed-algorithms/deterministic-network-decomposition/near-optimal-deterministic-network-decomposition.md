# Near-optimal deterministic network decomposition in $\tilde O(\log^2 n)$ rounds

Let $G = (V, E)$ be a simple connected graph with $n$ vertices and maximum degree $\Delta$, whose vertices carry distinct identifiers from $\{1, \dots, n^{O(1)}\}$. There is a deterministic LOCAL algorithm that computes a network decomposition with $O(\log n)$ colours and strong diameter $O(\log n)$ in $\tilde O(\log^2 n)$ rounds, where $\tilde O$ hides factors polynomial in $\log\log n$. This is near-optimal for decompositions used in the standard way, since processing a decomposition with $C$ colours and diameter $D$ costs $\Theta(C \cdot D)$ rounds, and, as Ghaffari and Grunau note, $C \cdot D = \tilde\Omega(\log^2 n)$ even for an ideal decomposition. The same work gives a separate deterministic LOCAL algorithm for maximal independent set in $\tilde O(\log^{5/3} n)$ rounds, below the $\log^2 n$ barrier of any method that runs through a network decomposition.

## Proof sketch

Both constructions rest on a new deterministic sampling theorem, a derandomized hitting-set selection with simultaneous upper and lower bounds on the number of sampled neighbours. The decomposition derandomizes the head-start clustering of Miller, Peng and Xu (each vertex joins the cluster minimizing distance minus head start): the $O(\log\log n)$ bits of each vertex's head start are fixed from the most significant bit down, each bit by one application of the sampling theorem that keeps the number of near-optimal head starts seen by each vertex small. The $O(\log n)$ colour classes are built simultaneously and recursively, reusing the higher bits of earlier head starts, so that later bits become cheaper and the total is $\tilde O(\log^2 n)$ instead of $\tilde O(\log^3 n)$; a base case builds partial decompositions from head-start functions of polylogarithmic badness. The MIS algorithm does not use the decomposition: it recursively computes an almost-maximal independent set from head-start functions of decreasing badness, again via the sampling theorem, with its own base case. The ruling set algorithm is another application of the same sampling theorem, not a subroutine of the decomposition.

## Depends on

- [Network decomposition with weak or strong diameter](network-decomposition-weak-strong-diameter.md)
- [The LOCAL model](../../distributed-execution-models/the-local-model.md)

## Sources

- M. Ghaffari, C. Grunau, "Near-Optimal Deterministic Network Decomposition and Ruling Set, and Improved MIS", FOCS 2024, arXiv:2410.19516, Theorems 1.3, 5.1 and 6.1 and Sections 1.5, 3, 5 and 6.
