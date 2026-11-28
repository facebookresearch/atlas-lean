# Stable models are supported models

Let $P$ be a [finite ground normal logic program](normal-logic-program.md). Every [stable model](../../../TheoryOfComputation/np-completeness/satisfiability/stable-model-existence/is-stable-model.md) of $P$ is a [supported model](supported-models.md) of $P$: each of its atoms is the head of a rule of $P$ whose positive body is contained in the model and whose negative body is disjoint from it. The converse fails: $p \leftarrow p$ has the supported model $\{p\}$, which is not stable.

**Proof.** Let $M$ be the least model of the [reduct](../../../TheoryOfComputation/np-completeness/satisfiability/stable-model-existence/reduct.md) $P^M$; it is a model of $P$ because [stable models are minimal models](stable-models-are-minimal-models.md). The least model of the definite program $P^M$ is the union of the iterates of its immediate-consequence operator from $\emptyset$, so each $a \in M$ is the head of a rule of $P^M$ whose body lies in $M$. That rule comes from a rule of $P$ with the same head and positive body whose negative body is disjoint from $M$, and the body of that rule is true in $M$.

## Depends on

- [Normal logic program](normal-logic-program.md)
- [Stable models of a normal logic program](../../../TheoryOfComputation/np-completeness/satisfiability/stable-model-existence/is-stable-model.md)
- [Supported models](supported-models.md)

## Proof depends on

- [Gelfond–Lifschitz reduct](../../../TheoryOfComputation/np-completeness/satisfiability/stable-model-existence/reduct.md)
- [Stable models are minimal models](stable-models-are-minimal-models.md)
- [Least Herbrand model of a definite logic program](../../../ComputerScience/programming-language-semantics/effects-modules-and-logic-programming/least-herbrand-model-of-a-definite-logic-program.md)

## Sources

- V. Lifschitz, "Foundations of logic programming", in G. Brewka (ed.), *Principles of Knowledge Representation*, CSLI Publications, 1996, pp. 69–127, <https://www.cs.utexas.edu/~vl/papers/flp.ps>, Proposition 3.3 and Corollary 1 to it.
- P. Hitzler, *Operator-based semantics for logic programs*, lecture notes, TU Dresden, winter semester 2004/05, <https://people.cs.ksu.edu/~hitzler/topics/teaching/ws04/plecture.pdf>, Theorem 2.22(i) and Program 2.20.
