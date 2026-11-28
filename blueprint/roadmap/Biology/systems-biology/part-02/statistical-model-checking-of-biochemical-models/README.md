# Statistical model checking of biochemical models

Stochastic simulations of rule-based signaling-pathway models can be checked against temporal-logic specifications ("protein X peaks within 2 hours and then decays") by treating each simulated trace as a Bernoulli trial and deciding, by sequential hypothesis testing, whether the satisfaction probability exceeds a threshold. The Bayesian version stops as soon as the Bayes factor is conclusive and bounds the error probability by the inverse of the stopping threshold.

## Articles

- [Bayesian sequential statistical model checking](bayesian-sequential-statistical-model-checking.md)
