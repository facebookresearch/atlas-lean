# Posterior Monte Carlo: statistical target and sampling error

Draw `θs 0, θs 1, …`
independently from the Bayes posterior `bayesPosterior κ π x` (positive evidence at `x`). For a
measurable `g` square-integrable under the posterior, the Monte Carlo average of `m > 0` draws is
unbiased for the posterior mean `∫ g d(posterior)` and has variance `Var_posterior(g) / m`.
