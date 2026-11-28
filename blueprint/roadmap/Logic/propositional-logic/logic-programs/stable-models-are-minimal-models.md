# Stable models are minimal models

Let $P$ be a [finite ground normal logic program](normal-logic-program.md). Every [stable model](../../../TheoryOfComputation/np-completeness/satisfiability/stable-model-existence/is-stable-model.md) $M$ of $P$ is a [minimal model](models-of-a-normal-logic-program.md) of $P$. The converse fails: $p \leftarrow \mathrm{not}\ q$, $q \leftarrow \mathrm{not}\ r$ has the minimal models $\{q\}$ and $\{p, r\}$, and only $\{q\}$ is stable.

**Proof.** Let $M$ be the least model of the [reduct](../../../TheoryOfComputation/np-completeness/satisfiability/stable-model-existence/reduct.md) $P^M$. *Model:* take a rule of $P$ whose body is true in $M$; then no atom of its negative body is in $M$, so the reduct contains the rule with its negative body deleted, whose positive body lies in $M$, and so its head is in $M$. *Minimal:* let $K \subseteq M$ be a model of $P$. A rule of $P^M$ comes from a rule of $P$ whose negative body is disjoint from $M$, hence from $K$; since $K$ satisfies that rule, it satisfies the rule of the reduct. So $K$ is a model of $P^M$, and $M \subseteq K$ because $M$ is its least model.

## Depends on

- [Normal logic program](normal-logic-program.md)
- [Stable models of a normal logic program](../../../TheoryOfComputation/np-completeness/satisfiability/stable-model-existence/is-stable-model.md)
- [Models of a normal logic program](models-of-a-normal-logic-program.md)

## Proof depends on

- [Gelfond–Lifschitz reduct](../../../TheoryOfComputation/np-completeness/satisfiability/stable-model-existence/reduct.md)

## Sources

- M. Gelfond and V. Lifschitz, "The stable model semantics for logic programming", in *Logic Programming: Proceedings of the Fifth International Conference and Symposium*, MIT Press, 1988, pp. 1070–1080, <https://www.cs.utexas.edu/~vl/papers/stable.ps>, Theorem 1 and its proof at the end of Section 2.
- V. Lifschitz, "Foundations of logic programming", in G. Brewka (ed.), *Principles of Knowledge Representation*, CSLI Publications, 1996, pp. 69–127, <https://www.cs.utexas.edu/~vl/papers/flp.ps>, Proposition 3.18 and the example (49) of Section 3.8.
- P. Hitzler, *Operator-based semantics for logic programs*, lecture notes, TU Dresden, winter semester 2004/05, <https://people.cs.ksu.edu/~hitzler/topics/teaching/ws04/plecture.pdf>, Theorem 2.22(ii).
