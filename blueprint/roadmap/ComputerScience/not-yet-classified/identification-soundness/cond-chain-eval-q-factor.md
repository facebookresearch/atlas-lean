# The conditional chain of a c-component

Let a Bayesian network whose nodes take values in
a finite nonempty type have latent node set `L`, let `σ` be a topological order of its latent
projection, let `S` be a c-component of the subgraph of the projection induced on a set `D` of
observed nodes, and let `P` be an expression that evaluates, against the observed law, to the
Q-factor `Q[D]` at every observed assignment. Then at every observed assignment `v` of positive
observed probability, the conditional chain of `P` over `S` along `σ` inside `D` (lines 6 and 7
of ID) evaluates to `Q[S]&#40;v)`. This covers Lemmas 7 and 8 of Shpitser and Pearl (AAAI 2006),
through Lemma 1 of Tian and Pearl (2002) applied in the subgraph on `D`.
