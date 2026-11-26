# Finding small and complete rewritings of conjunctive queries is NP-complete

Let $Q$ be a conjunctive query and $\mathcal V$ a set of conjunctive views, neither with built-in comparison atoms,
and let $k$ be smaller than the number of atoms in the body of $Q$. Each of the following problems is NP-complete:

1. whether some rewriting of $Q$ using $\mathcal V$ has fewer than $k$ atoms;
2. whether some rewriting of $Q$ using $\mathcal V$ has fewer than $k$ database-relation atoms;
3. whether $Q$ has a complete rewriting using $\mathcal V$.

## Depends on

- [Rewritings of conjunctive queries using views](rewritings-of-conjunctive-queries-using-views.md)
- [NP-complete decision problems](../../../TheoryOfComputation/complexity-classes/mahaney-s-theorem/npcomplete.md)

## Proof depends on

- [Locally minimal rewritings reuse the query's atoms, and their view atoms can use the query's variables](locally-minimal-rewritings-reuse-the-query-atoms.md)
- [Locally minimal complete rewritings have at most as many atoms as the query](complete-rewritings-have-at-most-as-many-atoms-as-the-query.md)
- [Chandra-Merlin containment criterion](../../not-yet-classified/conjunctive-queries/contained-iff-hom.md)
- [A query has a rewriting using a view exactly when its Boolean projection is contained in the view's](existence-of-a-rewriting-using-a-view.md)
- [CONJUNCTIVE QUERY CONTAINMENT is NP-complete](../../../TheoryOfComputation/not-yet-classified/part-01/part-10/conjunctive-query-containment/conjunctive-query-containment-np-complet.md)

## Sources

- A. Y. Levy, A. O. Mendelzon, Y. Sagiv and D. Srivastava, "Answering queries using views", *Proceedings of the 14th ACM Symposium on Principles of Database Systems (PODS)*, 1995, pp. 95–104, Proposition 3.1 (p. 97) and Theorem 3.7 with its proof, which reduces from the existence of a usage of a view (p. 99).
