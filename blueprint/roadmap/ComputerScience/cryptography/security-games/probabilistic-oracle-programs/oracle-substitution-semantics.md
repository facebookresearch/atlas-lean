# Oracle substitution: running a program against a simulated interface

Let $A$ be a probabilistic oracle program over an interface $(Q, R)$, and let $S$ assign to every query $q \in Q$ a probabilistic oracle program $S(q)$ over a second interface $(Q', R')$ returning an element of $R(q)$. Let $A[S]$ be the program over $(Q', R')$ obtained by replacing each query of $A$ by the corresponding program. Then for every stateful handler $h'$ of the second interface, running $A[S]$ against $h'$ gives the same joint distribution of output and final state as running $A$ against the stateful handler that answers $q$ by running $S(q)$ against $h'$. Moreover, if $A$ makes at most $B$ queries and each $S(q)$ makes at most $c$ queries, then $A[S]$ makes at most $Bc$ queries, and the private coins of $A$ are preserved.

## Proof sketch

Induction on the program tree: $\mathsf{return}$ and $\mathsf{sample}$ commute with substitution, and a query node unfolds into the run of $S(q)$ followed by the continuation, which is exactly how the induced handler is defined. The query bound follows by the same induction.

## Depends on

- [Probabilistic oracle program and its semantics against a stateful handler](probabilistic-oracle-program.md)
- [Query bound](../oracle-algorithms/is-query-bounded.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
