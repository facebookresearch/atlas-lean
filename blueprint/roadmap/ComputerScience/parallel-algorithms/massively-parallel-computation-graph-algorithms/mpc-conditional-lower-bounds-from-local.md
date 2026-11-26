# LOCAL lower bounds transfer to component-stable MPC algorithms

Assuming the one-versus-two-cycle conjecture, every component-stable MPC algorithm with strongly sublinear local memory (one whose output on each connected component depends only on that component and the vertices' identifiers) that solves a graph problem $\Pi$ with a LOCAL lower bound of $T(n)$ rounds requires $\Omega(\log T(n))$ rounds. In particular, maximal independent set, maximal matching and constant-approximate minimum vertex cover require $\Omega(\log\log n)$ rounds for such algorithms.

## Proof sketch

Given a fast MPC algorithm, distinguish one cycle from two cycles by building, in $O(1)$ rounds, an instance consisting of copies of the hard LOCAL instance glued along the input cycle structure: if the MPC algorithm runs in $o(\log T)$ rounds, its output on a component depends only on balls of radius $2^{o(\log T)} = T^{o(1)}$ reachable by graph exponentiation, so it behaves like a LOCAL algorithm with fewer than $T$ rounds unless it uses global information, which in the one-cycle case would distinguish the two cases.

## Depends on

- [The one-cycle versus two-cycle conjecture](one-cycle-versus-two-cycle-conjecture.md)
- [Deterministic and randomized LOCAL complexity of an LCL problem](../../concurrent-systems-and-protocols/local-distributed-algorithms/lcl-problems-and-the-locality-landscape/lcl-deterministic-randomized-complexity.md)

## Proof depends on

- [Maximal matching and MIS require Omega(min(Delta, log n / log log n)) deterministic rounds](../../concurrent-systems-and-protocols/local-distributed-algorithms/lcl-problems-and-the-locality-landscape/maximal-matching-mis-delta-lower-bound.md)

## Sources

- M. Ghaffari, F. Kuhn, J. Uitto, "Conditional Hardness Results for Massively Parallel Computation from Distributed Lower Bounds", FOCS 2019.
