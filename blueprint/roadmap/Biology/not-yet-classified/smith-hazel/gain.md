# Gain

The totalized truncation-selection shift
`conditionalMeanShift μ M.aggregate (standardizedUpperEvent μ (M.index b) z)`, i.e., the integral
of `H` under the normalized conditional measure on `{ω | μ[I_b] + z * σ_{I_b} ≤ I_b ω}` minus the
unnormalized integral `∫ H dμ`. When `μ` is a probability measure, `H` is integrable, and the
standardized upper event is measurable with positive mass, this equals the genetic gain: the mean
of `H` among selected outcomes minus the population mean of `H`.
