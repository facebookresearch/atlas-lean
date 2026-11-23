# Rate Root

The rate root `b̂(a)`: the positive solution of the rate score equation
`∑ᵢ (a / b - (a + kᵢ) / (b + sᵢ)) = 0` at the shape `a`, and `0` if there is none. For `a > 0`,
positive size factors and some positive count it exists and is unique
(`exists_rateScore_eq_zero`, `rateScore_eq_zero_unique`), see `rateRoot_spec`; with a common size
factor `σ` it is the closed form `σ a / M` (`rateRoot_const`).
