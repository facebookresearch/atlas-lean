# A definite program has exactly one stable model

Let $P$ be a [definite](normal-logic-program.md) finite ground program. Then $P$ has exactly one [stable model](../../../TheoryOfComputation/np-completeness/satisfiability/stable-model-existence/is-stable-model.md), its [least model](../../../ComputerScience/programming-language-semantics/effects-modules-and-logic-programming/least-herbrand-model-of-a-definite-logic-program.md).

**Proof.** A definite program has no negative bodies, so its [reduct](../../../TheoryOfComputation/np-completeness/satisfiability/stable-model-existence/reduct.md) with respect to any set of atoms is $P$ itself. Hence $M$ is stable exactly when $M$ is the least model of $P$.

## Depends on

- [Stable models of a normal logic program](../../../TheoryOfComputation/np-completeness/satisfiability/stable-model-existence/is-stable-model.md)
- [Least Herbrand model of a definite logic program](../../../ComputerScience/programming-language-semantics/effects-modules-and-logic-programming/least-herbrand-model-of-a-definite-logic-program.md)
- [Normal logic program](normal-logic-program.md)

## Proof depends on

- [Gelfond–Lifschitz reduct](../../../TheoryOfComputation/np-completeness/satisfiability/stable-model-existence/reduct.md)

## Sources

- P. Hitzler, *Operator-based semantics for logic programs*, lecture notes, TU Dresden, winter semester 2004/05, <https://people.cs.ksu.edu/~hitzler/topics/teaching/ws04/plecture.pdf>, Theorem 2.22(iii).
- M. Gelfond and V. Lifschitz, "The stable model semantics for logic programming", in *Logic Programming: Proceedings of the Fifth International Conference and Symposium*, MIT Press, 1988, pp. 1070–1080, <https://www.cs.utexas.edu/~vl/papers/stable.ps>, Section 2 (the definition of stable models) and Section 3: a program without negation has a unique stable model, its minimal Herbrand model.
