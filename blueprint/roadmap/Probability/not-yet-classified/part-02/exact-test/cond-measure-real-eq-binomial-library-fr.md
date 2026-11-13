# Binomial conditioning

Under the hypotheses of `measureReal_add_eq_inter_eq`, given a
total `X + Y = n` of positive probability, the condition-1 count is binomial:
`P(X = k | X + Y = n) = Bin(n, s₁ / (s₁ + s₂)){k}`. The law does not depend on the nuisance rate
`r`.

For `r > 0` this is `ProbabilityTheory.cond_measureReal_eq_binomial`
(`MathlibExt.Probability.Distributions.Multinomial`) at rates `s₁ r, s₂ r`, after
`s₁ r / (s₁ r + s₂ r) = s₁ / (s₁ + s₂)`. This restatement takes the success probability in the
`libraryFraction` form and assumes only that the total has positive probability, so it also
covers `r = 0` (where the total `0` is certain), which that theorem's `0 < a + b` excludes.

## Sources

- Lehmann–Romano (2005), §4.5; Przyborowski–Wileński (1940).
