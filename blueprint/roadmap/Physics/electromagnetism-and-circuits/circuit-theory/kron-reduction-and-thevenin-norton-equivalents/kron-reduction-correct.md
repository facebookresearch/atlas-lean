# Kron reduction of a positive definite conductance matrix

Let `m` (ports) and `p` (interior nodes) be finite index sets and `A`, `B` and `D` real matrices of
sizes `m × m`, `m × p` and `p × p` such that the block matrix `G = [[A, B], [Bᵀ, D]]` is symmetric
positive definite; then `D` is invertible. Let `K = A - B D⁻¹ Bᵀ`. If `A φ_P + B φ_I = j_P` and
`Bᵀ φ_P + D φ_I = j_I`, then:

- `K` is positive definite;
- the reduced port equation `K φ_P = j_P - B D⁻¹ j_I` holds;
- `φ_I = D⁻¹ (j_I - Bᵀ φ_P)`;
- the dissipation splits as `φ · (G φ) = φ_P · (K φ_P) + j_I · (D⁻¹ j_I)`, where `φ = (φ_P, φ_I)`.
