# Constant propagation, constant folding and definite initialization

Constant propagation is the monotone framework over the flat lattice $\mathbb{Z}_\top^\bot$ for each variable, with transfer functions that evaluate assignments abstractly; its solution is sound: at every program point, a variable mapped to a constant $c$ has the value $c$ in every execution reaching that point. Replacing expressions whose operands are known constants by their values preserves the behavior of the program. Definite-initialization analysis, the forward must-analysis of assigned variables, is sound: under a semantics in which reading an uninitialized variable is an error, programs accepted by the analysis never read an uninitialized variable.

## Proof depends on

- [Monotone frameworks and the worklist algorithm](monotone-frameworks-and-the-worklist-algorithm.md)
- [Simulation diagrams for compiler correctness](../compiler-correctness/simulation-diagrams-for-compiler-correctness.md)

## Expansion

This page becomes ready once:

- While language whose small-step semantics makes reading an uninitialized variable an error (statement prerequisite; not yet stated)
- The abstract transfer functions of both analyses and the concrete domain must be stated explicitly

## Sources

- A. Møller and M. I. Schwartzbach, *Static Program Analysis*, lecture notes, Aarhus University, 2022, <https://cs.au.dk/~amoeller/spa/>
- F. Nielson, H. R. Nielson and C. Hankin, *Principles of Program Analysis*, Springer, 1999
