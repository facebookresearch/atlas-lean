# Reconstruction from a reduced solution solves the block equations

Let `m` (ports) and `p` (interior nodes) be finite index sets, `A`, `B` and `D` real matrices of
sizes `m × m`, `m × p` and `p × p` with `D` invertible, and `K = A - B D⁻¹ Bᵀ`. If
`K φ_P = j_P - B D⁻¹ j_I`, then the interior potentials `φ_I = D⁻¹ (j_I - Bᵀ φ_P)` satisfy
`A φ_P + B φ_I = j_P` and `Bᵀ φ_P + D φ_I = j_I`.
