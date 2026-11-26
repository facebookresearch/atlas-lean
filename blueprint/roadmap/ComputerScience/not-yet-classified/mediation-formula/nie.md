# Average natural indirect effect

**Average natural indirect effect** `NIE(x, x*; Y) = E(Y_{x*, Z_x}) - E(Y_{x*})` (P01,
Definition 7, eq. (20)). This is not the `TE - NDE` convention of
`LinearMediation.MediationModel.naturalIndirectEffect x₀ x₁`, which equals `-nie ... x₀ x₁`
in every model and agrees with the reversed call `nie ... x₁ x₀` only in additive models
(module docstring).
