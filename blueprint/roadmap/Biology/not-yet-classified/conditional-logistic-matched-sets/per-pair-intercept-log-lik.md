# Incidental-parameter log-likelihood of independent pairs

The log-likelihood of the
discordant pairs, with a separate nuisance intercept for every pair (not a valid estimating
likelihood for `β`): a pair with the case exposed and the control unexposed contributes
`log (σ(α + β) (1 - σ α))`, and a pair with the reverse contributes `log (σ α (1 - σ(α + β)))`.
Each term takes the two subjects of a pair to be independent, and the sum is the joint
log-likelihood when the pairs are independent of one another. Here `σ` is the logistic function
`Real.sigmoid`.
