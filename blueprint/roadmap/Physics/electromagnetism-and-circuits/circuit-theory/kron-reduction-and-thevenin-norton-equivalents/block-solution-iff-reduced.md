# Block nodal equations are equivalent to the reduced port equation

Let `m` (ports) and `p` (interior nodes) be finite index sets, `A`, `B` and `D` real matrices of
sizes `m × m`, `m × p` and `p × p` with `D` invertible, and `K = A - B D⁻¹ Bᵀ` the Schur complement.
For all potentials `φ_P`, `φ_I` and injections `j_P`, `j_I`, the block system `A φ_P + B φ_I = j_P`,
`Bᵀ φ_P + D φ_I = j_I` holds if and only if the reduced port equation `K φ_P = j_P - B D⁻¹ j_I` and
the reconstruction `φ_I = D⁻¹ (j_I - Bᵀ φ_P)` hold.
