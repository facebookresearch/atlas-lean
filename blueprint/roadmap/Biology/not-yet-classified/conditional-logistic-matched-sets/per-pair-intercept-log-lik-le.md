# Maximizer of the incidental-parameter log-likelihood

**Maximizer of the incidental-parameter log-likelihood** (Breslow and Day 1980, p. 250). For
`n₁₀ > 0` discordant pairs with the case exposed and `n₀₁ > 0` with the control exposed, let
`β̂ = 2 log (n₁₀ / n₀₁)`, so that `e^β̂ = (n₁₀ / n₀₁)²`. Then the incidental-parameter
log-likelihood, with a separate intercept for every pair, is maximized at `β = β̂` with every
intercept equal to `-β̂ / 2`: for all intercepts `α₁₀, α₀₁` and every `β`, its value is at most
the value at that point. Thus the maximizing odds ratio `(n₁₀ / n₀₁)²` is the square of the
conditional estimate `n₁₀ / n₀₁` of `pairedConditionalLogLik_max` (moving any positive estimate
`≠ 1` farther from `1`; this algebraic identity for the maximizer does not by itself state a
statistical expectation/bias theorem).

## Sources

- Breslow and Day (1980), p. 250.
