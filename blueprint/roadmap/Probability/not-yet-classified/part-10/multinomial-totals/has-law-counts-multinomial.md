# The cell counts of `n` i.i.d. draws are multinomial, as a law

Under the hypotheses of
`measureReal_counts_eq_multinomialReal`, the count vector `i ↦ #{k < n | X k = i}` has law
`multinomial n p` (the PMF of the merged `Distributions.Multinomial`). The probability-vector
conditions `hp₀`, `hp₁` are needed only to form that PMF.
