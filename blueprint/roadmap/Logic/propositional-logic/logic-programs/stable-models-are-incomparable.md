# Stable models are incomparable

Let $P$ be a [finite ground normal logic program](normal-logic-program.md). If $X$ and $Y$ are [stable models](../../../TheoryOfComputation/np-completeness/satisfiability/stable-model-existence/is-stable-model.md) of $P$ and $X \subseteq Y$, then $X = Y$. So the stable models of a program form an antichain under inclusion.

**Proof.** If $X \subseteq Y$, every rule deleted in forming the [reduct](../../../TheoryOfComputation/np-completeness/satisfiability/stable-model-existence/reduct.md) $P^X$ is also deleted in forming $P^Y$, so $P^Y \subseteq P^X$. The [least model](../../../ComputerScience/programming-language-semantics/effects-modules-and-logic-programming/least-herbrand-model-of-a-definite-logic-program.md) $X$ of $P^X$ is a model of the smaller program $P^Y$, so $Y$, the least model of $P^Y$, is contained in $X$.

## Depends on

- [Normal logic program](normal-logic-program.md)
- [Stable models of a normal logic program](../../../TheoryOfComputation/np-completeness/satisfiability/stable-model-existence/is-stable-model.md)

## Proof depends on

- [Gelfond–Lifschitz reduct](../../../TheoryOfComputation/np-completeness/satisfiability/stable-model-existence/reduct.md)
- [Least Herbrand model of a definite logic program](../../../ComputerScience/programming-language-semantics/effects-modules-and-logic-programming/least-herbrand-model-of-a-definite-logic-program.md)

## Sources

- V. Lifschitz, "Foundations of logic programming", in G. Brewka (ed.), *Principles of Knowledge Representation*, CSLI Publications, 1996, pp. 69–127, <https://www.cs.utexas.edu/~vl/papers/flp.ps>, Proposition 3.1.
- P. Hitzler, *Operator-based semantics for logic programs*, lecture notes, TU Dresden, winter semester 2004/05, <https://people.cs.ksu.edu/~hitzler/topics/teaching/ws04/plecture.pdf>, Theorem 2.25(i) (the Gelfond–Lifschitz operator is antitonic).
