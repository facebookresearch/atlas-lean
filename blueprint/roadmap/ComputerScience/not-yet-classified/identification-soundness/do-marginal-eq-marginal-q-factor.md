# The effect as a marginal of a Q-factor

For a Bayesian network whose nodes take values in
a finite nonempty type, with latent node set `L`, sets `X` and `Y` of observed nodes and an
observed assignment `v`, the effect `P_x(y)` read at `v` equals the sum of the Q-factor
`Q[O ∖ X]` over the values of the nodes of `(O ∖ X) ∖ Y`, the other observed nodes fixed at
their values in `v`, where `O` is the set of all observed nodes. No disjointness of `X` and `Y`
is assumed.
