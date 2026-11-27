# Soundness of Andersen's pointer analysis

For an imperative language with heap allocation at labelled allocation sites, Andersen's analysis generates inclusion constraints between points-to sets (for $x = \&y$, $x = y$, $x = {*}y$ and ${*}x = y$). The least solution of these constraints over-approximates every points-to fact that can arise in an execution: if a variable or abstract cell can hold a pointer to an object allocated at site $\ell$ in some reachable state, then $\ell$ is in its computed points-to set.

## Proof depends on

- [Monotone frameworks and the worklist algorithm](monotone-frameworks-and-the-worklist-algorithm.md)

## Expansion

This page becomes ready once:

- Structural operational semantics (statement prerequisite; not yet stated)
- Pointer language with labelled allocation sites, its operational semantics and the allocation-site abstraction of heap cells (statement prerequisite; not yet stated)

## Sources

- A. Møller and M. I. Schwartzbach, *Static Program Analysis*, lecture notes, Aarhus University, 2022, <https://cs.au.dk/~amoeller/spa/>
- L. O. Andersen, *Program Analysis and Specialization for the C Programming Language*, PhD thesis, University of Copenhagen, 1994
