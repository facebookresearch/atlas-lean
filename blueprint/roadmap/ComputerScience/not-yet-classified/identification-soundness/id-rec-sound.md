# The recursion invariant of ID

Let a Bayesian network whose nodes take values in a finite
nonempty type have latent node set `L`, let `σ` be a topological order of its latent projection,
and suppose the observed law is strictly positive at every observed assignment. Let `D` be a set
of observed nodes, `X` and `Y` disjoint subsets of `D`, and `P` an expression that evaluates,
against the observed law, to the Q-factor `Q[D]` at every observed assignment. If the recursion
`idRec` of ID, called on `Y`, `X`, `D` and `P`, returns an expression `e`, then at every observed
assignment `v`, `e` evaluates to the sum of `Q[D ∖ X]` over the values of the nodes of
`(D ∖ X) ∖ Y`: the effect of `do(X)` on `Y` in the sub-model on `D`. Nothing is claimed when
`idRec` fails. This is the induction behind Theorem 5 of Shpitser and Pearl (AAAI 2006), with
their Lemmas 4, 5, 6 and 8 for the recursive calls.
