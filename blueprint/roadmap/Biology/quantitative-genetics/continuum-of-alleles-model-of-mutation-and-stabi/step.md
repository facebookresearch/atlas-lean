# One generation of selection followed by mutation

For [model parameters](params.md), one generation applies [selection](select.md) and then
[mutation](mutate.md) to a measure `ν` on `ℝ`: `T ν = (1 - μ) ν_w + μ (ν_w ∗ N(0, γ²))`, where
`ν_w = w ν / ∫ w dν`, which is the zero measure when `w` is not `ν`-integrable or `ν = 0`.
