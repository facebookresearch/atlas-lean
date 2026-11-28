# The causal effect of an intervention in a Bayesian network

For a Bayesian network whose
nodes take values in a finite nonempty type, with latent node set `L`, sets `X` and `Y` of
observed nodes and an observed assignment `v`, the effect `P_x(y)` at `v` is the probability that
the observed nodes of `Y` take their values in `v` after the intervention `do(X = v)` on the
observed nodes of `X`, all other nodes, latent or observed, summed out (`x` and `y` are the values
of `v` on `X` and `Y`). The intervention is the surgery `BayesNet.mutilateSet`, which replaces the
table of each node of `X` by the point mass at its value in `v`: the submodel `M_x` of Shpitser
and Pearl (AAAI 2006, pp. 1220–1221).
