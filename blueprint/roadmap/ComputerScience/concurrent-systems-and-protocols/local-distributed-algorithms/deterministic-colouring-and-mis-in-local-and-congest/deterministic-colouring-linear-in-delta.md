# Deterministic (Delta+1)-colouring in O(Delta + log* n) rounds

Let $G = (V, E)$ be a simple connected graph with $n$ vertices and maximum degree $\Delta$, whose vertices carry distinct identifiers from $\{1, \dots, n^{O(1)}\}$. There is a deterministic LOCAL algorithm that computes a proper $(\Delta + 1)$-colouring in $O(\Delta + \log^* n)$ rounds. Furthermore, using local conflict colouring, the round complexity can be improved to $O(\sqrt{\Delta} \log^{2.5} \Delta + \log^* n)$, so the dependence on $\Delta$ is sublinear.

## Proof sketch

Compute an $O(\Delta^2)$-colouring by Linial's colour reduction, then compute a defective colouring with $O(1)$ colours and defect $\Delta/2$ (each vertex has at most $\Delta/2$ same-coloured neighbours), recurse on each colour class with half the degree and combine the palettes; the arboricity-based recursion yields $O(\Delta)$ rounds. For the sublinear bound, colour vertices via a local conflict colouring framework in which each vertex has a list and a conflict structure, and solve it with an iterative trial procedure whose number of iterations scales with $\sqrt{\Delta}$ up to polylogarithmic factors.

## Depends on

- [The (deg + 1)-list-coloring problem (D1LC)](../../../randomized-algorithms/palette-sparsification-and-sublinear-coloring/degree-plus-one-list-coloring.md)
- [The LOCAL model](../../distributed-execution-models/the-local-model.md)

## Proof depends on

- [Linial's colour reduction to O(Delta^2) colours in O(log* n) rounds](linial-colour-reduction.md)

## Sources

- L. Barenboim, M. Elkin, F. Kuhn, "Distributed (Delta+1)-Coloring in Linear (in Delta) Time", SIAM Journal on Computing 43(1) (2014); STOC 2009.
- P. Fraigniaud, M. Heinrich, A. Kosowski, "Local Conflict Coloring", FOCS 2016, arXiv:1511.01287.
