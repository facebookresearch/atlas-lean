# Ancestral restriction of an effect

Let a Bayesian network whose nodes take values in a
finite nonempty type have latent node set `L`, and let `A ⊆ H` and `Y` be sets of observed nodes
such that every parent in `H` of a node of `A`, in the latent projection, lies in `A`, and
`H ∩ Y ⊆ A`. Then at every observed assignment `v`, the sum of the Q-factor `Q[H]` over the
values of the nodes of `H ∖ Y` equals the sum of `Q[A]` over the values of the nodes of
`A ∖ Y`, the other nodes fixed at their values in `v`. This justifies lines 2 and 3 of ID
(Shpitser and Pearl, AAAI 2006, Lemmas 5 and 6) through Lemma 3 of Tian and Pearl's technical
report R-290-L, with no semi-Markovian hypothesis; the source proves line 3 by rule 3 of the
do-calculus instead.
