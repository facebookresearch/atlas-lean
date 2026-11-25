# Correctness of the Braun et al. SSA construction

The SSA construction of Braun, Buchwald, Hack, Leißa, Mallon and Zwinkau works directly on a program in control-flow-graph form.
- It numbers values locally within each block.
- It looks up the definition of a variable recursively in the predecessor blocks, creating a $\varphi$-function only when a use or another $\varphi$-function asks for it.
- It removes trivial $\varphi$-functions, those whose operands, other than the $\varphi$-function itself, are all one value.

Its output, in the senses of [dominance and static single assignment form](dominance-and-static-single-assignment-form.md), has these properties:

1. **Pruned.** The output is in pruned SSA form for every input, because $\varphi$-functions are created only on demand.
2. **Minimal for reducible inputs.** A program in SSA form with a reducible control-flow graph and no trivial $\varphi$-functions is in minimal SSA form. A graph is reducible if every cycle has a node that dominates all other nodes of the cycle. Hence the construction produces minimal SSA form for reducible inputs.
3. **Semantic equivalence.** For a functional variant of the algorithm over an abstract control-flow-graph representation, the output is semantically equivalent to the input under a small-step semantics. This has been proved in Isabelle/HOL, together with minimality for reducible inputs.

For irreducible control flow, a post pass that removes redundant strongly connected sets of $\varphi$-functions restores minimality.

## Depends on

- [Dominance and static single assignment form](dominance-and-static-single-assignment-form.md)

## Sources

- M. Braun, S. Buchwald, S. Hack, R. Leißa, C. Mallon and A. Zwinkau, "Simple and efficient construction of static single assignment form", *Compiler Construction (CC 2013)*, LNCS 7791, Springer, 2013: Section 2 (the algorithm), Section 3.2 and Lemma 1 (minimal SSA form for arbitrary control flow), Section 4 (pruned SSA form; Definition 3, Lemmas 2 and 3 and Theorem 1, minimality for reducible graphs).
- S. Ullrich and D. Lohner, "Verified construction of static single assignment form", *Archive of Formal Proofs*, 2016, <https://www.isa-afp.org/entries/Formal_SSA.html>: the abstract states semantic equivalence under a small-step semantics and minimality for reducible inputs; see also their paper at CC 2016.
