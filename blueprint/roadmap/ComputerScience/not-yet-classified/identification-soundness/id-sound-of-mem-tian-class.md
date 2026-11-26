# Soundness of the ID algorithm for a fixed causal diagram

Let `G` be an acyclic directed
mixed graph on the observed nodes of a latent set `L`, with a topological order `σ`, and let `X`
and `Y` be disjoint sets of observed nodes. If the ID algorithm, run on `G` with the order `σ`,
returns an expression `e` for the effect of `do(X)` on `Y`, then for every Bayesian network of
`tianClass L G` (node values in one finite nonempty type, no latent node a descendant of an
observed node, latent projection `G`, observed law strictly positive at every observed
assignment), `e` evaluated against that network's observed law equals its effect `P_x(y)` at
every observed assignment. The descendant condition is Tian and Pearl's 2002 semi-Markovian
hypothesis (AAAI-02, p. 568), which `ID_sound` shows is not needed. Nothing is claimed when ID
returns a failure pair.
