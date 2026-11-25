# Per Pair Intercept Log Lik

The incidental-parameter log-likelihood of the discordant pairs, with a separate nuisance
intercept for every pair (not a valid estimating likelihood for `β`): a pair
with the case exposed and the control unexposed contributes
`log (σ(α + β) (1 - σ α))`, and a pair with the reverse contributes
`log (σ α (1 - σ(α + β)))`. Here `σ` is the logistic
function `Real.sigmoid`.
