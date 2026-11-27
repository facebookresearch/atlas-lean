# LOCAL lower bounds transfer to component-stable MPC algorithms

Call an MPC algorithm *component-stable* if the output of each vertex $v$ depends only on $v$, on the initial distribution among machines and the identifiers of the connected component of $v$, and on the shared randomness. Let $\Pi$ be a graph problem with a $T(n)$-round lower bound in the randomized LOCAL model with shared randomness, where $T(n) \le \log^{\gamma} n$ for a constant $\gamma \in (0, 1)$. If some component-stable MPC algorithm with strongly sublinear local memory $S = n^{\alpha}$ and $\mathrm{poly}(n)$ global memory solves $\Pi$ in $o(\log T(n))$ rounds, then such MPC algorithms can distinguish one $n$-vertex cycle from two $n/2$-vertex cycles in $o(\log n)$ rounds. Hence, assuming the one-versus-two-cycle conjecture, every such component-stable algorithm needs $\Omega(\log T(n))$ rounds; in particular, any constant approximation of maximum matching (so also maximal matching, even on trees), any constant approximation of minimum vertex cover, and maximal independent set require $\Omega(\log\log n)$ rounds.

## Proof sketch

The LOCAL lower bound gives two graphs whose radius-$t$ neighbourhoods of a node agree, for some $t$ with $\log t = \Theta(\log T)$, while the node's output distributions under any correct algorithm differ; so a component-stable MPC algorithm running in $o(\log T)$ rounds, too few to gather radius-$t$ balls by graph exponentiation, must be sensitive to changes at distance more than $t$. This sensitivity, applied to inputs built from the two graphs and an $s$-$t$ path, yields an $o(\log n)$-round strongly sublinear MPC algorithm for $D$-diameter $s$-$t$ connectivity with $D = T(n)$, and hence for one cycle versus two cycles. The matching, vertex-cover and MIS bounds lift the randomized $\Omega(\sqrt{\log n/\log\log n})$ LOCAL lower bounds of Kuhn, Moscibroda and Wattenhofer, which also hold with shared randomness.

## Depends on

- [The massively parallel computation model](massively-parallel-computation-model.md)
- [The one-cycle versus two-cycle conjecture](one-cycle-versus-two-cycle-conjecture.md)
- [The LOCAL model](../../concurrent-systems-and-protocols/distributed-execution-models/the-local-model.md)
- [Deterministic and randomized LOCAL complexity of an LCL problem](../../concurrent-systems-and-protocols/local-distributed-algorithms/lcl-problems-and-the-locality-landscape/lcl-deterministic-randomized-complexity.md)

## Proof depends on

- [Randomized MIS requires Omega(sqrt(log n / log log n)) rounds](../../concurrent-systems-and-protocols/local-distributed-algorithms/lcl-problems-and-the-locality-landscape/randomized-mis-near-logarithmic-lower-bound.md)
- [Locality lower bound for approximating minimum vertex cover](../../concurrent-systems-and-protocols/local-distributed-algorithms/deterministic-colouring-and-mis-in-local-and-congest/kmw-vertex-cover-lower-bound.md)

## Sources

- M. Ghaffari, F. Kuhn, J. Uitto, "Conditional Hardness Results for Massively Parallel Computation from Distributed Lower Bounds", FOCS 2019.
