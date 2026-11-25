# Gain

The totalized truncation-selection shift
`conditionalMeanShift μ M.aggregate (standardizedUpperEvent μ (M.index b) z)`, i.e., the integral
of `H` under the scaled restriction `μ[|s]` on `s = {ω | μ[I_b] + z * σ_{I_b} ≤ I_b ω}`
(normalized when `0 < μ s < ∞`, and zero when `μ s = 0` or `μ s = ∞`) minus the unnormalized
integral `∫ H dμ`. When `μ` is a probability measure, `H` is integrable, and `s` is measurable
with positive mass, this equals the genetic gain: the mean of `H` among selected outcomes minus
the population mean of `H`.
