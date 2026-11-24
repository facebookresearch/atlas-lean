# Paired Unconditional Log Lik

The unconditional log-likelihood of the discordant pairs with one intercept per pair: a pair
with the case exposed and the control unexposed contributes
`log (expit(α + β) (1 - expit α))`, and a pair with the reverse contributes
`log (expit α (1 - expit(α + β)))`.
