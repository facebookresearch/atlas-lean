# Cosine integrals over the box vanish for m ≥ 1

Cosine interval integral at positive integer frequency: for `m ≥ 1`,
`∫ x in 0..L, cos (m * π * x / L) = 0`, by the fundamental theorem of
calculus (Mathlib `intervalIntegral.integral_eq_sub_of_hasDerivAt`) with
antiderivative `(L / (m * π)) * sin (m * π * x / L)`.
