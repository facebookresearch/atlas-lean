# Ab Hamiltonian

The AB Hamiltonian in frequency units (Hz), `H = -νA I_zA - νB I_zB + J I_A · I_B`. The
Zeeman terms have the sign of `zeemanEnergy` (`E = -γ hbar B0 m`), so for positive resonance
frequencies `νA`, `νB` the state `α` (`m = +1/2`) lies below `β`. The spin-1/2 operators are
`I_k = σ_k / 2` (`k = 0, 1, 2` for `x, y, z`), with Physlib's Pauli matrices
`σ_k = PauliMatrix.pauliMatrix (Sum.inr k)`. On the two-spin space `I_kA = I_k ⊗ 1` and
`I_kB = 1 ⊗ I_k` (Kronecker products), so `I_kA I_kB = I_k ⊗ I_k` by the mixed-product rule
`Matrix.mul_kronecker_mul`, and the coupling term is `J ∑ k, I_k ⊗ I_k`.
