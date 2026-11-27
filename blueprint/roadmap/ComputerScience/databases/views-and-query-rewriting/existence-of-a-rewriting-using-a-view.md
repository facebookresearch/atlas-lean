# A query has a rewriting using a view exactly when its Boolean projection is contained in the view's

Let $Q$ and $V$ be conjunctive queries, possibly with built-in comparison atoms ($=, \ne, <, \le$), and write $\pi_\emptyset(Q)$ for the
Boolean query that holds on a database exactly when $Q$ has an answer there. There is a rewriting of $Q$ using $V$
if and only if $\pi_\emptyset(Q) \subseteq \pi_\emptyset(V)$, that is, on every database on which $V$ is empty, $Q$ is
empty as well.

## Depends on

- [Rewritings of conjunctive queries using views](rewritings-of-conjunctive-queries-using-views.md)

## Sources

- A. Y. Levy, A. O. Mendelzon, Y. Sagiv and D. Srivastava, "Answering queries using views", *Proceedings of the 14th ACM Symposium on Principles of Database Systems (PODS)*, 1995, pp. 95–104, Proposition 3.1 (p. 97).
