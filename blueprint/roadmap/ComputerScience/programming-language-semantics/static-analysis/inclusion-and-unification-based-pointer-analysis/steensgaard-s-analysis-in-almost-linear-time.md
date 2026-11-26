# Steensgaard's analysis in almost linear time

Steensgaard's points-to analysis, a flow-insensitive interprocedural analysis based on a non-standard type system whose types represent sets of locations, runs in space linear and time $O(N\,\alpha(N, N))$ in the size $N$ of the input program, where $\alpha$ is an inverse of Ackermann's function. Its results are those of a flow-insensitive alias analysis that assumes alias relations to be reflexive and transitive.

**Proof idea.** The analysis starts with a distinct type variable for every variable and merges types, represented as equivalence-class representatives in a union-find structure, as the typing rules require, processing each statement once. The number of representatives created and of merges performed is linear in the size of the program, and $N$ find operations cost $O(N\,\alpha(N, N))$ in total.

The [unification constraints](steensgaard-s-unification-constraints.md) of the simplified formulation are likewise solved with a union-find structure.

## Depends on

- [Steensgaard's unification constraints](steensgaard-s-unification-constraints.md)

## Sources

- B. Steensgaard, "Points-to analysis in almost linear time", *Conference Record of the 23rd ACM Symposium on Principles of Programming Languages (POPL 1996)*, <https://www.cs.cornell.edu/courses/cs711/2005fa/papers/steensgaard-popl96.pdf>: the abstract (almost linear time, results equivalent to a flow-insensitive alias analysis assuming reflexive and transitive alias relations) and Section 5.3 ("Complexity": linear space, $O(N\,\alpha(N, N))$ time from the cost of find operations on the equivalence-class representatives).
- A. Møller and M. I. Schwartzbach, *Static Program Analysis*, lecture notes, Aarhus University, version of October 15, 2026, <https://cs.au.dk/~amoeller/spa/>: Section 11.4 (solving the constraints with the union-find solver of Section 3.3).
