# Raw failure-and-choice trees

For a type $\alpha$, the carrier of explicit nondeterminism over $\alpha$ is the type of raw failure-and-choice trees with leaves in $\alpha$: the free monad on the [signature of explicit nondeterminism](nondet-f.md), whose operations are failure, with no continuation, and binary choice, with two. It is free on the signature only: there is no quotient by the monoid laws of Plotkin and Pretnar's Section 6.4, so for instance choice between a return of $x$ and failure is an operation node, not the leaf $x$.
