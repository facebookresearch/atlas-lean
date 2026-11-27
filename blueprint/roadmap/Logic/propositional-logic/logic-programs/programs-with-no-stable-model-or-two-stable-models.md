# Programs with no stable model or two stable models

1. The program $\{p \leftarrow \mathrm{not}\ p\}$ has no [stable model](../../../TheoryOfComputation/np-completeness/satisfiability/stable-model-existence/is-stable-model.md).
2. The program $\{p \leftarrow \mathrm{not}\ q,\ q \leftarrow \mathrm{not}\ p\}$ has exactly the two stable models $\{p\}$ and $\{q\}$.

So a normal program may have no stable model or several.

**Proof.** Check the two interpretations of the first program and the four of the second. For part 1, the [reduct](../../../TheoryOfComputation/np-completeness/satisfiability/stable-model-existence/reduct.md) with respect to $\emptyset$ is $\{p \leftarrow\}$, whose least model is $\{p\} \ne \emptyset$, and the reduct with respect to $\{p\}$ is empty, whose least model is $\emptyset \ne \{p\}$. For part 2, the reduct with respect to $\{p\}$ is $\{p \leftarrow\}$, with least model $\{p\}$, and symmetrically for $\{q\}$; the reduct with respect to $\emptyset$ is $\{p \leftarrow,\ q \leftarrow\}$ and the one with respect to $\{p, q\}$ is empty, so neither set is stable.

## Depends on

- [Stable models of a normal logic program](../../../TheoryOfComputation/np-completeness/satisfiability/stable-model-existence/is-stable-model.md)

## Proof depends on

- [Gelfond–Lifschitz reduct](../../../TheoryOfComputation/np-completeness/satisfiability/stable-model-existence/reduct.md)

## Sources

- V. Lifschitz, "Foundations of logic programming", in G. Brewka (ed.), *Principles of Knowledge Representation*, CSLI Publications, 1996, pp. 69–127, <https://www.cs.utexas.edu/~vl/papers/flp.ps>, Section 3.1 (Proposition 3.1 and its Corollary: a program has no answer set, or only the inconsistent one, or consistent answer sets only) and Section 3.8 (normal programs without answer sets).
- M. Gelfond and V. Lifschitz, "The stable model semantics for logic programming", in *Logic Programming: Proceedings of the Fifth International Conference and Symposium*, MIT Press, 1988, pp. 1070–1080, <https://www.cs.utexas.edu/~vl/papers/stable.ps>, Section 2 (the definition of stable models, applied to the examples there).
