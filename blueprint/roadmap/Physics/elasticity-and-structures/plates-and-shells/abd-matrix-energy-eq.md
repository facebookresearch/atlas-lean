# Ply decomposition of the laminate energy

For `n ∈ ℕ`, interfaces `z_0, …, z_n` (heights from the reference plane) and ply stiffnesses
`Q̄_0, …, Q̄_{n−1}` (real `3 × 3` matrices in global axes, ply `i` occupying `[z_i, z_{i+1}]`), if
every `Q̄_i` is symmetric, then for all `ε⁰, κ ∈ ℝ³` the energy of the
[block stiffness matrix](abd-matrix.md) `[[A, B], [B, D]]` is

`(ε⁰, κ) · ([[A, B], [B, D]] (ε⁰, κ)) = ∑_i (h_i E_i + (h_i³ / 12) κ · (Q̄_i κ))`,

where `E_i = (ε⁰ + z̄_i κ) · (Q̄_i (ε⁰ + z̄_i κ))`, with the [ply thickness](ply-thickness.md)
`h_i = z_{i+1} − z_i` and the [ply midplane](ply-midplane.md) `z̄_i = (z_i + z_{i+1}) / 2`. The
interfaces need not increase.
