# Locally minimal complete rewritings have at most as many atoms as the query

Let $Q$ be a conjunctive query whose body has $p$ atoms and $\mathcal V$ a set of conjunctive views, neither with
built-in comparison atoms. Every locally minimal complete rewriting of $Q$ using $\mathcal V$ has at most $p$ atoms.
Since views identical to the database relations may be added, every locally minimal rewriting of $Q$ has at most $p$
atoms.

## Depends on

- [Rewritings of conjunctive queries using views](rewritings-of-conjunctive-queries-using-views.md)

## Proof depends on

- [Chandra-Merlin containment criterion](../../not-yet-classified/conjunctive-queries/contained-iff-hom.md)

## Sources

- A. Y. Levy, A. O. Mendelzon, Y. Sagiv and D. Srivastava, "Answering queries using views", *Proceedings of the 14th ACM Symposium on Principles of Database Systems (PODS)*, 1995, pp. 95–104, Lemma 3.5 with its proof (p. 99).
