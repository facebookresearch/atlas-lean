# Cramér–Rao inequality with nonsingular information

Under the hypotheses of
`sq_fderiv_le_inner_fisherInformation_mul` in every direction, if the Fisher information
`I(θ)` is invertible, then `Var_θ T ≥ ⟪∇g(θ), I(θ)⁻¹ ∇g(θ)⟫`, the matrix form
`∇gᵀ I⁻¹ ∇g ≤ Var T`. Invertibility follows from positive definiteness
(`isUnit_of_inner_self_pos`); for singular information this statement is not claimed, and the
directional form still applies.

## Sources

- Rao (1945), Cramér (1946), ch. 32; Lehmann & Casella (1998), Theorem 2.6.6.
