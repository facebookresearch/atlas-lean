# One generation of selection followed by mutation

For [model parameters](params.md), with selection width `Vₛ > 0`, mutation probability
`0 < μ < 1` and mutational standard deviation `γ > 0`, one generation applies
[selection](select.md) and then [mutation](mutate.md) to a measure `ν` on `ℝ`:
`T ν = (1 - μ) ν_w + μ (ν_w ∗ N(0, γ²))`, where `ν_w = w ν / ∫ w dν` with the fitness
`w(x) = exp(-x² / (2 Vₛ))`, and `ν_w` is the zero measure when `w` is not `ν`-integrable or
`ν = 0`.
