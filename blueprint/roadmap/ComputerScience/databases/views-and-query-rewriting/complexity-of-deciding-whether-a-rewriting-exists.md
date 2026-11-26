# Complexity of deciding whether a rewriting using views exists

Let $Q$ be a conjunctive query and $\mathcal V$ a set of conjunctive views. If $Q$ may contain built-in comparison
atoms and the views contain none, deciding whether a rewriting of $Q$ using $\mathcal V$ exists is NP-complete. If
both $Q$ and the views may contain built-in comparison atoms, the problem is $\Pi_2^p$-complete.

## Depends on

- [Rewritings of conjunctive queries using views](rewritings-of-conjunctive-queries-using-views.md)
- [NP-complete decision problems](../../../TheoryOfComputation/complexity-classes/mahaney-s-theorem/npcomplete.md)
- [The universal levels of the polynomial hierarchy](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/pi-k.md)

## Proof depends on

- [A query has a rewriting using a view exactly when its Boolean projection is contained in the view's](existence-of-a-rewriting-using-a-view.md)
- [Chandra-Merlin containment criterion](../../not-yet-classified/conjunctive-queries/contained-iff-hom.md)

## Sources

- A. Y. Levy, A. O. Mendelzon, Y. Sagiv and D. Srivastava, "Answering queries using views", *Proceedings of the 14th ACM Symposium on Principles of Database Systems (PODS)*, 1995, pp. 95–104, Proposition 3.2 (p. 97).
