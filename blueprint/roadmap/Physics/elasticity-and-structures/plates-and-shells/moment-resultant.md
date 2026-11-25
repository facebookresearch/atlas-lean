# Moment resultant of a laminate

For `n ∈ ℕ`, interfaces `z_0, …, z_n` (heights from the reference plane) and ply stiffnesses
`Q̄_0, …, Q̄_{n−1}` (real `3 × 3` matrices in global axes, ply `i` occupying `[z_i, z_{i+1}]`), and
`ε⁰, κ ∈ ℝ³`, `M = ∑_i ∫_{z_i}^{z_{i+1}} s Q̄_i (ε⁰ + s κ) ds`, the sum over plies of the integral
of the height times the [ply stress](ply-stress.md) (oriented integrals).
