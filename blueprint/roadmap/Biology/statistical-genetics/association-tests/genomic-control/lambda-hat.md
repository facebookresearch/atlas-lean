# Lambda Hat

The mean-based genomic-control estimate `λ̂ = (1 / m) ∑ₖ zₖ²` computed from the scores
`z : Fin m → ℝ` of all `m` genes (the 1-df statistics are `zₖ²`). For `m = 0` genes the value is
`0` (`0 / 0`), not a mean of any statistics.
