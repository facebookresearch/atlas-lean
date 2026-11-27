# LOCAL lower bounds transfer to component-stable MPC algorithms

Call a randomized MPC algorithm *component-stable* if its output at each vertex $v$ is a deterministic function of the topology and identifiers of the connected component of $v$, of $v$ itself, of the number $n$ of vertices and the maximum degree $\Delta$ of the whole input graph, and of the shared random seed. Call a class of graphs *normal* if it is closed under removing vertices and under disjoint unions; the class of all graphs and the class of forests are normal, the class of trees is not. Let $\Pi$ be an $O(1)$-replicable graph problem (a class that contains every locally checkable labelling problem and the constant approximations of maximum matching and of minimum vertex cover) that has a $T(N, \Delta)$-round lower bound in the randomized LOCAL model with shared randomness on graphs from a normal class $\mathcal{G}$ with input size estimate $N$ and maximum degree $\Delta$, where $T$ is *constrained*: $T(N, \Delta) = O(\log^{\gamma} N)$ for a constant $\gamma \in (0, 1)$ and $T(N^c, \Delta) \le c\, T(N, \Delta)$ for every $c \ge 1$. If some component-stable MPC algorithm with strongly sublinear local memory $S = n^{\alpha}$, for a constant $\alpha \in (0, 1)$, and $\mathrm{poly}(n)$ global memory solves $\Pi$ on $n$-vertex graphs of $\mathcal{G}$ with maximum degree $\Delta$ in $o(\log T(n, \Delta))$ rounds with success probability at least $1 - 1/n$, then a low-space MPC algorithm distinguishes one $n$-vertex cycle from two $n/2$-vertex cycles in $o(\log n)$ rounds with success probability at least $1 - 1/n$. Hence, assuming the one-versus-two-cycle conjecture, every such component-stable algorithm needs $\Omega(\log T(n, \Delta))$ rounds; in particular, any constant approximation of maximum matching (so also maximal matching), even on forests, any constant approximation of minimum vertex cover, and maximal independent set require $\Omega(\log\log n)$ rounds. A LOCAL lower bound on trees lifts only to forests, since the lifting builds disjoint unions of induced subgraphs of the hard instances.

## Proof sketch

The LOCAL lower bound gives two graphs whose radius-$t$ neighbourhoods of a node agree, for some $t$ with $\log t = \Theta(\log T)$, while the node's output distributions under any correct algorithm differ; so a component-stable MPC algorithm running in $o(\log T)$ rounds, too few to gather radius-$t$ balls by graph exponentiation, must be sensitive to changes at distance more than $t$. This sensitivity, applied to inputs built from the two graphs and an $s$-$t$ path, yields an $o(\log n)$-round strongly sublinear MPC algorithm for $D$-diameter $s$-$t$ connectivity with $D = T(n, \Delta)$, and hence for one cycle versus two cycles; replicability and normality guarantee that the disjoint unions built in this step are again valid inputs of $\Pi$ in $\mathcal{G}$. The matching, vertex-cover and MIS bounds lift the randomized $\Omega(\sqrt{\log n/\log\log n})$ LOCAL lower bounds of Kuhn, Moscibroda and Wattenhofer, which also hold with shared randomness.

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
- A. Czumaj, P. Davies, M. Parter, "Component Stability in Low-Space Massively Parallel Computation", PODC 2021, arXiv:2106.01880, Definitions 7, 9, 13 and 26, Lemmas 10 and 12, Theorems 14 and 28.
