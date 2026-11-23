# One generation as a map on probability measures

For [model parameters](params.md), with selection width `Vₛ > 0`, mutation probability
`0 < μ < 1` and mutational standard deviation `γ > 0`, the [generation map](step.md)
`T ν = (1 - μ) ν_w + μ (ν_w ∗ N(0, γ²))`, where `ν_w = w ν / ∫ w dν` and
`w(x) = exp(-x² / (2 Vₛ))`, sends every probability measure `ν` on `ℝ` to a probability measure:
for such `ν` the mean fitness `∫ w dν` is positive and finite (as `0 < w ≤ 1`), so `ν_w` is a
probability measure. This is `T` as a map from the probability measures on `ℝ` to themselves;
its domain does not contain the zero measure.
