# Selection step of the continuum-of-alleles model

For [model parameters](params.md) with selection width `Vₛ > 0` and a measure `ν` on `ℝ` (in the
model, the distribution of allelic effects), selection reweights `ν` by the
[fitness](fitness.md) `w`, with `0 < w ≤ 1`: `ν_w = w ν / ∫ w dν`. For a probability measure `ν`
this is a probability measure. The definition accepts every measure: if `w` is not `ν`-integrable
(which needs an infinite `ν`) or `ν = 0`, the result is the zero measure.
