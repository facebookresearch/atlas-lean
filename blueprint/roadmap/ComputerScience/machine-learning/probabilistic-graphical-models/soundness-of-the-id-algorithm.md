# Soundness of the ID algorithm

Let a Bayesian network whose nodes take values in a finite
nonempty type have latent node set `L`, let `σ` be a topological order of its latent projection
onto the observed nodes, and suppose the observed law is strictly positive at every observed
assignment. Let `X` and `Y` be disjoint sets of observed nodes. If the ID algorithm (Shpitser and
Pearl, AAAI 2006, Fig. 3), run on the latent projection with the order `σ`, returns an expression
`e` for the effect of `do(X)` on `Y`, then `e`, evaluated against the observed law, equals the
effect `P_x(y)` at every observed assignment `v`, with `x` and `y` the values of `v` on `X` and
`Y`. No semi-Markovian hypothesis is needed. When ID returns a failure pair `(F, F')` instead,
nothing is claimed: neither that `(F, F')` is a hedge nor that `P_x(y)` is not identified.

## Sources

- I. Shpitser and J. Pearl, *Identification of Joint Interventional Distributions in Recursive Semi-Markovian Causal Models*, AAAI 2006 (technical report R-327), Theorem 5. <https://ftp.cs.ucla.edu/pub/stat_ser/r327.pdf>
- I. Shpitser and J. Pearl, *Identification of Conditional Interventional Distributions*, UAI 2006 (technical report R-329), Section 4, where the result is restated. <https://ftp.cs.ucla.edu/pub/stat_ser/r329-uai.pdf>
