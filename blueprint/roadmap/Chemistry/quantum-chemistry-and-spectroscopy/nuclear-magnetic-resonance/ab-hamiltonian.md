# Hamiltonian of the AB spin system

The AB Hamiltonian in frequency units (Hz), `H = -νA I_zA - νB I_zB + J I_A · I_B`, a `4 × 4`
complex matrix on the two-spin space `ℂ² ⊗ ℂ²` with basis `αα, αβ, βα, ββ`. The Zeeman terms have
the sign of the Zeeman energy `E = -γ hbar B0 m`, so for positive resonance frequencies `νA`, `νB`
the state `α` (`m = +1/2`) lies below `β`. The spin-1/2 operators are `I_k = σ_k / 2` for
`k = x, y, z`, with the Pauli matrices `σ_x = [[0, 1], [1, 0]]`, `σ_y = [[0, -i], [i, 0]]` and
`σ_z = [[1, 0], [0, -1]]` in the basis `α, β`. On the two-spin space `I_kA = I_k ⊗ 1` and
`I_kB = 1 ⊗ I_k` (Kronecker products), so `I_kA I_kB = I_k ⊗ I_k` by the mixed-product rule, and the
coupling term is `J ∑_k I_k ⊗ I_k`.
