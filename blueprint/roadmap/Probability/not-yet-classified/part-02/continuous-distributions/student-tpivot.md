# Student TPivot

The Student-t pivot `√n (x̄ₙ - μ) / sₙ` for the mean `μ`. Where `sₙ = 0` it is `0`, by
Lean's convention for division by zero; under `StudentTPivotLaw` this happens only on a null set
(`StudentTPivotLaw.ae_sampleStdDev_pos`).
