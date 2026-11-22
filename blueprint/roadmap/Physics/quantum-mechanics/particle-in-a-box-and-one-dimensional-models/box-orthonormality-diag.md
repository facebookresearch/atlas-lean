# Box states are normalized

Diagonal orthonormality: `∫ x in 0..L, boxFunction n * boxFunction n = 1`,
via `sin^2 = (1 - cos 2θ)/2` (Mathlib `Real.cos_two_mul`,
`Real.sin_sq_add_cos_sq`) and `cos_integral_pos`.
