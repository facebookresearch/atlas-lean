# Colouring and MIS in graphs of bounded arboricity via H-partitions

Let $G = (V, E)$ be a simple connected graph with $n$ vertices and maximum degree $\Delta$, whose vertices carry distinct identifiers from $\{1, \dots, n^{O(1)}\}$. For every $\varepsilon > 0$ there is a deterministic LOCAL algorithm that computes an H-partition with $\ell = O(\log n / \varepsilon)$ classes and degree bound $A = (2 + \varepsilon)\, a(G)$ in $O(\log n / \varepsilon)$ rounds. Consequently an $O(a(G))$-colouring can be computed deterministically in $O(a(G) \log n)$ rounds, an $O(a(G)^{1 + \varepsilon})$-colouring in $O(\log n)$ rounds, and a maximal independent set in $O(a(G) + a(G)^{\varepsilon} \log n)$ rounds; in particular planar graphs admit deterministic $O(\log n)$-round algorithms for colouring with $O(1)$ colours and for MIS in $O(\log n)$ rounds.

## Proof sketch

In each round, all remaining vertices with at most $(2 + \varepsilon) a$ remaining neighbours join the next class and are removed; since the average degree of every subgraph is below $2a$, a constant fraction $\Omega(\varepsilon)$ of the remaining vertices qualifies, so $O(\log n/\varepsilon)$ classes suffice. Colouring proceeds class by class from the last to the first, each vertex choosing a colour distinct from its at most $A$ already-coloured higher neighbours, combined with Linial-type colour reduction within classes; MIS uses the orientation to break symmetry.

## Depends on

- [Arboricity and H-partitions](arboricity-and-h-partitions.md)

## Proof depends on

- [Linial's colour reduction to O(Delta^2) colours in O(log* n) rounds](linial-colour-reduction.md)

## Sources

- L. Barenboim, M. Elkin, "Sublogarithmic distributed MIS algorithm for sparse graphs using Nash-Williams decomposition", Distributed Computing 22 (2010); PODC 2008.
