# Expected loss is PD times the conditional expected loss

Let `μ` be a probability measure, `D` a measurable default event with `P(D) = μ(D) ≠ 0`, and
`EAD` (exposure at default) and `LGD` (loss given default) real functions such that
`EAD · LGD` is integrable on `D`. Then the expected loss `∫ 1_D EAD LGD dμ` equals the default
probability `P(D)` times the conditional expected loss `∫ EAD LGD dμ[·|D]`, where
`μ[·|D] = μ(· ∩ D) / P(D)` is the conditional probability given `D`. No independence between
`EAD` and `LGD` is assumed.
