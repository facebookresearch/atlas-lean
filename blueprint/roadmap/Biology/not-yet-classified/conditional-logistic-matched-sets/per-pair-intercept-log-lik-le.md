# The incidental-parameter estimate is biased

**The incidental-parameter estimate is biased** (Breslow and Day 1980, p. 250). For `n₁₀ > 0`
discordant pairs with the case exposed and `n₀₁ > 0` with the control exposed, let
`β̂ = 2 log (n₁₀ / n₀₁)`, so that `e^β̂ = (n₁₀ / n₀₁)²`. Then the incidental-parameter
log-likelihood, with a separate intercept for every pair, is maximized at `β = β̂` with every
intercept equal to `-β̂ / 2`: for all intercepts `α₁₀, α₀₁` and every `β`, its value is at most the
value at that point. The maximizing odds ratio is the square of the conditional estimate
`n₁₀ / n₀₁` of `pairedConditionalLogLik_max`, which shows the bias of estimating `β` jointly with
one nuisance intercept per pair.

## Sources

- Breslow and Day (1980), p. 250.
