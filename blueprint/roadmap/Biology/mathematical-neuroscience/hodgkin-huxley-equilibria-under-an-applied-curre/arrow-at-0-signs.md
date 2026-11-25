# At rest the linear and constant coefficients and Δ₃ are positive

At the resting voltage `V = 0`, the characteristic quartic `μ⁴ + p₁ μ³ + p₂ μ² + p₃ μ + p₄` of the
[arrowhead entries at V](arrow-at.md), the entries of the squid Jacobian at the
[resting state](../hodgkin-huxley-model/rest.md), has [linear coefficient](coef-3.md) `p₃ > 0`,
[constant coefficient](coef-4.md) `p₄ > 0` and positive [third Hurwitz determinant](hdet.md)
`Δ₃ = p₁ p₂ p₃ - p₃² - p₁² p₄`. Together with `p₁ > 0`, which holds at every voltage
(`p₁ = -a + k₁ + k₂ + k₃` with `a < 0` and `k₁, k₂, k₃ > 0`), these are the
[Routh–Hurwitz conditions](is-hurwitz-of-hdet-pos.md).
