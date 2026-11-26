# Complete rewriting of unions of conjunctive queries is NP-complete

Let $Q$ and the views of $\mathcal V$ be unions of conjunctive queries without built-in comparison atoms. Deciding
whether $Q$ has a complete rewriting using $\mathcal V$ is NP-complete.

## Depends on

- [Rewritings of conjunctive queries using views](rewritings-of-conjunctive-queries-using-views.md)
- [NP-complete decision problems](../../../TheoryOfComputation/complexity-classes/mahaney-s-theorem/npcomplete.md)
- [Positive relational algebra = unions of conjunctive queries = positive existential calculus](../relational-calculus/positive-relational-algebra-unions-of-conjunctive-queries-po.md)

## Proof depends on

- [Finding small and complete rewritings of conjunctive queries is NP-complete](finding-small-and-complete-rewritings-is-np-complete.md)
- [Containment of unions of conjunctive queries](../conjunctive-queries/cores-and-minimization/containment-of-unions-of-conjunctive-queries.md)

## Sources

- A. Y. Levy, A. O. Mendelzon, Y. Sagiv and D. Srivastava, "Answering queries using views", *Proceedings of the 14th ACM Symposium on Principles of Database Systems (PODS)*, 1995, pp. 95–104, Theorem 3.9 (p. 100), which relies on the containment test for unions of conjunctive queries of Sagiv and Yannakakis.
