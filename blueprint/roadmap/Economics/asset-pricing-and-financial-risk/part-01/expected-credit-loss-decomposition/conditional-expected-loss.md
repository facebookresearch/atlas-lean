# Expected loss conditional on default

For a measure `μ`, a default event `D` and real functions `EAD` (exposure at default) and `LGD`
(loss given default), the conditional expected loss is `∫ EAD LGD dμ[·|D]`, the integral of
`EAD · LGD` against the conditional measure `μ[·|D] = μ(D)⁻¹ μ(· ∩ D)`; when
`0 < μ(D) < ∞` it is `(1 / μ(D)) ∫_D EAD LGD dμ`. If `μ(D) = 0` (or `μ(D) = ∞`), the
conditional measure is the zero measure and the conditional expected loss is `0`; it is also
`0` when `EAD · LGD` is not integrable for `μ[·|D]`.
