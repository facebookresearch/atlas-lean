# Probabilistic oracle program and its semantics against a stateful handler

Fix an *oracle interface*: a set $Q$ of queries and, for each $q \in Q$, a set $R(q)$ of possible responses. A *probabilistic oracle program* returning values in $X$ is a finite tree built from three constructors: $\mathsf{return}(x)$; $\mathsf{query}(q, k)$, which asks $q$ and continues with $k(r)$ on response $r \in R(q)$; and $\mathsf{sample}(n, k)$, which draws a private uniform element $i$ of a finite set of size $n$ and continues with $k(i)$. Programs form a monad under sequential composition. Given a *stateful probabilistic handler* $h$ assigning to each state $\sigma$ and query $q$ a distribution on $R(q) \times \Sigma$, the *run* of a program from state $\sigma_0$ is the distribution on $X \times \Sigma$ obtained by answering queries with $h$, threading the state, and sampling the private coins uniformly. A stateless handler is the case of a singleton state space.

## Depends on

- [Adaptive oracle algorithms](../oracle-algorithms/oracle-comp.md)
- [Running against a stateful randomized oracle](../lazy-sampling-and-the-prp-prf-switching-lemma/run-state.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- M. Bellare and P. Rogaway, "The Security of Triple Encryption and a Framework for Code-Based Game-Playing Proofs", Advances in Cryptology (EUROCRYPT 2006), LNCS 4004, 2006.
