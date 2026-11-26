# A solution of the block nodal equations solves the reduced equation

Let `m` (ports) and `p` (interior nodes) be finite index sets, `A`, `B` and `D` real matrices of
sizes `m × m`, `m × p` and `p × p` with `D` invertible, and `K = A - B D⁻¹ Bᵀ`. If
`A φ_P + B φ_I = j_P` and `Bᵀ φ_P + D φ_I = j_I`, then `K φ_P = j_P - B D⁻¹ j_I`.
