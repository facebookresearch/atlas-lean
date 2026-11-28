# Syntactic soundness

Let `exn` be the exception type. Every term reachable in any number
of steps from a closed term of type `A` has type `A`, and is final or takes a step; in particular
a final term it reaches, a value or an uncaught exception `raise v`, has type `A`. This is Wright
and Felleisen's Theorem 5.10 for every reachable term, specialized to one anonymous exception.
