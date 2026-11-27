# L* termination, correctness and query bound

Let $U$ be a regular language over a finite alphabet $\Sigma$ whose minimal DFA has $n$ states, presented by a
minimally adequate teacher whose counterexamples have length at most $m$. Angluin's algorithm $L^*$ terminates
and outputs a DFA isomorphic to the minimal DFA of $U$. It makes at most $n$ equivalence queries and a number of
membership queries polynomial in $\lvert\Sigma\rvert$, $n$ and $m$, and its running time, counting each query as one
step, is polynomial in $\lvert \Sigma \rvert$, $n$ and $m$ (Angluin, Theorem 6; for a fixed alphabet, polynomial in
$m$ and $n$).

## Depends on

- [Minimally adequate teacher and observation tables](minimally-adequate-teacher-and-observation-tables.md)

## Proof depends on

- [Angluin's observation-table theorem](../angluin-s-observation-table-theorem.md)

## Sources

- Learning Regular Sets from Queries and Counterexamples (Angluin, Inf. Comput. 1987), Berkeley course copy — Angluin; Information and Computation, Theorem 6. <https://people.eecs.berkeley.edu/~dawnsong/teaching/s10/papers/angluin87.pdf>
