# Simulation-based validation of Bayesian models

Checks that an implementation of a Bayesian evolutionary model (simulator plus MCMC sampler) is correct, by drawing parameters from the prior, simulating data, running inference, and testing calibration properties that hold exactly when the posterior is computed correctly: nominal coverage of credible intervals, uniformity of the rank of the true value among posterior draws, and calibration of clade posterior probabilities.

- [Nominal coverage of credible intervals under the prior predictive](nominal-coverage-of-credible-intervals-under-the-prior-predictive.md)
- [Rank uniformity for tree topologies via distance to a reference tree](rank-uniformity-in-simulation-based-calibration.md)
