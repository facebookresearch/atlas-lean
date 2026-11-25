# Perm Rows

`σ A`: the left product `(σ⁻¹).permMatrix ℝ * A` under Mathlib's permutation-matrix convention,
with entries `(permRows σ A) i j = A (σ⁻¹ i) j` (equivalently `(σ A)_{σ(i) j} = A_{ij}`), so that
its interaction graph replaces each edge `j → i` of `G(A)` by `j → σ(i)`.
