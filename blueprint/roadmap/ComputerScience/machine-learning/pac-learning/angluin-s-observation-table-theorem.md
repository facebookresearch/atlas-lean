# Angluin's observation-table theorem

Let $(S, E, T)$ be an observation table over a finite alphabet that is closed and consistent. Then the
acceptor $M(S, E, T)$ constructed from the table is a well-defined deterministic finite automaton
consistent with $T$, and every other deterministic finite automaton consistent with $T$ that has at most
as many states is isomorphic to $M(S, E, T)$.

## Depends on

- [Minimally adequate teacher and observation tables](exact-learning-from-queries/minimally-adequate-teacher-and-observation-tables.md)

## Sources

- D. Angluin, *Learning regular sets from queries and counterexamples*, Inform. and Comput. 75 (1987) 87–106, Theorem 1 and Lemmas 2–4. <https://people.eecs.berkeley.edu/~dawnsong/teaching/s10/papers/angluin87.pdf>
