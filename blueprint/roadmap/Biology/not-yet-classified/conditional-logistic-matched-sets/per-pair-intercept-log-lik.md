# Per Pair Intercept Log Lik

The incidental-parameter log-likelihood of the discordant pairs, with a separate nuisance
intercept for every pair (not a valid estimating likelihood for `β`): a pair
with the case exposed and the control unexposed contributes
`log (expit(α + β) (1 - expit α))`, and a pair with the reverse contributes
`log (expit α (1 - expit(α + β)))`.
