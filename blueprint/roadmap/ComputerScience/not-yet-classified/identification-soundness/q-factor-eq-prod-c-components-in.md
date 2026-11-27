# C-component factorization inside a vertex set

For a Bayesian network whose nodes take
values in a finite nonempty type, with latent node set `L`, a set `H` of observed nodes and an
observed assignment `v`, the Q-factor `Q[H]&#40;v)` is the product of the Q-factors `Q[S]&#40;v)` over
the c-components `S` of the subgraph of the latent projection induced on `H`. This is line 4 of
ID (Shpitser and Pearl, AAAI 2006, Lemma 4), with no semi-Markovian hypothesis.
