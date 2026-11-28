# Syntactic soundness for abort-free programs

Let `T` be the answer type. Every term
reachable in any number of steps from an abort-free closed term `e` of type `A` has type `A` at
answer type `A`, and is a value or takes a step; in particular a value reached from `e` has type
`A`. The reached terms are typed at answer type `A`, the type of the program, rather than at `T`,
since the continuation that a `callcc` step passes aborts with a term of type `A`. This is Wright
and Felleisen's Theorem 6.6 for every reachable term, with the answer typed as in its proof.
