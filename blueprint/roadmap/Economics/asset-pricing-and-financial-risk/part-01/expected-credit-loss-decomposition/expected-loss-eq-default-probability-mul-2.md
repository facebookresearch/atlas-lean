# Expected loss as PD times conditional mean LGD times a constant EAD

Let `μ` be a probability measure, `D` a measurable default event with `P(D) = μ(D) ≠ 0`, and
`EAD` (exposure at default) and `LGD` (loss given default) real functions such that `EAD`
equals a constant `ead` on `D` and both `EAD · LGD` and `LGD` are integrable on `D`. Then the
expected loss `∫ 1_D EAD LGD dμ` equals `P(D) · E[LGD | D] · ead`, where
`E[LGD | D] = ∫ LGD dμ[·|D]` is the mean of `LGD` under the conditional probability
`μ[·|D] = μ(· ∩ D) / P(D)`. No independence of `LGD` from anything is assumed.
