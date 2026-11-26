# Inverse rotations give the same norm

Let `R` be a commutative ring, `n : ℕ`, `N=n+1`, and `ρ=finRotate N`. In `R[S_N]`, put `N_n =
∑ r : Fin N, sign(ρ^r.val) [ρ^r.val]`, with signs cast from `ℤ` to `R`. The inverse-power sum
satisfies `∑ r : Fin N, sign((ρ^r.val)⁻¹) [(ρ^r.val)⁻¹] = signedCyclicNormElement R n`.
