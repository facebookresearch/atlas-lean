# Standardization, treated arm

**Standardization, treated arm** (the g-formula for a finite covariate): under conditional
exchangeability `T ⊥ Y₁ | X` with overlap (`StronglyIgnorable μ T Y₁ X`), for a measurable,
integrable treated potential outcome `Y₁` and a covariate `X` with finitely many values,
`E[Y₁] = ∑_x P(X = x) E[Y | T, X = x]` with `Y = observed T Y₀ Y₁` (consistency) and
`E[· | T, X = x]` the mean under the conditional law `μ[|T ∩ {X = x}]`. Covariate values of
probability zero contribute `0`.
