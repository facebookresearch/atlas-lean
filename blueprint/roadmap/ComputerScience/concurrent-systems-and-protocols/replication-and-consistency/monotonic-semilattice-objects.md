# Monotonic semilattice objects

A *state-based replicated object* is a tuple $(S, s^0, q, u, m)$ of a set of states $S$, an initial state $s^0 \in S$, query methods $q$ that read a state, update methods $u$, each a function $S \to S$ applied at one replica, and a merge function $m : S \times S \to S$ applied when a replica receives another replica's state. It is a *monotonic semilattice object* if $S$, ordered by $\le$, is a join-semilattice; $m(s, s') = s \sqcup s'$; every update is inflationary ($s \le u(s)$ for every state $s$); and queries have no side effects: the state after a query is equivalent to the state before it, two states being equivalent when all queries return the same results on them.

## Sources

- M. Shapiro, N. Preguiça, C. Baquero and M. Zawirski, "Conflict-free replicated data types", *SSS 2011*, LNCS 6976, Springer, 2011; INRIA research report RR-7687, Sections 2.1 and 2.3, Definition 2.4
