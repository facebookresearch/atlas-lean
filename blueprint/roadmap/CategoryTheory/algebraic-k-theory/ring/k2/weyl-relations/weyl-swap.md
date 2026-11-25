# Weyl swap

Weyl index swap: `w_{ij}(u) = w_{ji}(-u⁻¹)`. Exact equality in `St(R)`,
preserving coefficient, sign, inverse, and multiplication orientation, including
characteristic two. The proof reuses the existing
`weyl_conj_x_ij` / `weyl_conj_x_ji` identities (which already use the private
auxiliary `k := max i j + 1` and Chevalley commutator expansions for opposite
roots) and finishes by the elementary swapping calculation
`w_{ij}(u) x_{ij}(u) w_{ij}(u)⁻¹ = x_{ji}(-u⁻¹)`,
`w_{ij}(u) x_{ji}(-u⁻¹) w_{ij}(u)⁻¹ = x_{ij}(u)`,
hence `w_{ij}(u)² = w_{ji}(-u⁻¹) w_{ij}(u)` and `w_{ij}(u)=w_{ji}(-u⁻¹)`.
No exact torus index-swap, `weyl(u)^2 = torus(-1)`, or cocycle-subgroup
claim is made here; those may carry a central defect and belong downstream.
