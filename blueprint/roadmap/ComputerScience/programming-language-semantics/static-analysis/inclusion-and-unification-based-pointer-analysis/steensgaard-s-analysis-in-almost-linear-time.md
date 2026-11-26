# Steensgaard's analysis in almost linear time

Steensgaard's points-to analysis, a flow-insensitive interprocedural analysis based on a non-standard type system whose types represent sets of locations, runs in space linear and time $O(N\,\alpha(N, N))$ in the size $N$ of the input program, where $\alpha$ is an inverse of Ackermann's function. Its results are those of a flow-insensitive alias analysis that assumes alias relations to be reflexive and transitive.

**Proof idea.** The algorithm starts with a distinct type variable for every variable, represents types by equivalence-class representatives in a union-find structure, and processes each statement once. Where a typing rule requires the type of one location to be at least that of another, it performs a *conditional join*: the two types are joined at once if the source type is not $\bot$, and otherwise the target is recorded in a pending set of the source, to be joined when the source type becomes non-$\bot$. The number of representatives created and of joins performed is linear in $N$, and with linking by rank and path compression the [union-find operations](../../../data-structures/disjoint-sets-and-dynamic-trees/disjoint-set-data-structure/run-empty-cost-le-inverse-ackermann.md) cost $O(N\,\alpha(N, N))$ in total.

The [unification constraints](steensgaard-s-unification-constraints.md) of the simplified intraprocedural formulation, which has no conditional joins, are solved with a union-find structure as well; the bound above is stated for the original algorithm.

## Depends on

- [Steensgaard's unification constraints](steensgaard-s-unification-constraints.md)

## Proof depends on

- [Tarjan–van Leeuwen bound for union by rank with path compression](../../../data-structures/disjoint-sets-and-dynamic-trees/disjoint-set-data-structure/run-empty-cost-le-inverse-ackermann.md)

## Sources

- B. Steensgaard, "Points-to analysis in almost linear time", *Conference Record of the 23rd ACM Symposium on Principles of Programming Languages (POPL 1996)*, <https://www.cs.cornell.edu/courses/cs711/2005fa/papers/steensgaard-popl96.pdf>: the abstract (almost linear time, results equivalent to a flow-insensitive alias analysis assuming reflexive and transitive alias relations) Section 5, Figures 5 and 6 (the typing-based algorithm with conditional joins and pending sets) and Section 5.3 ("Complexity": linear space, $O(N\,\alpha(N, N))$ time from the cost of find operations on the equivalence-class representatives).
- A. Møller and M. I. Schwartzbach, *Static Program Analysis*, lecture notes, Aarhus University, version of October 15, 2026, <https://cs.au.dk/~amoeller/spa/>: Section 11.4 (solving the constraints with the union-find solver of Section 3.3).
