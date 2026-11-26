# Permutations are uniquely a tail permutation followed by inverse rotation

For n : ℕ, cyclicFirstEquiv is a bijection Fin(n+1) × Perm(Fin n) ≃ Perm(Fin(n+1)). It sends
(j,σ) to fixFirst(σ)·shift_j⁻¹. Its inverse sends τ to j=τ⁻¹(0) and the tail permutation of
τ·shift_j, which fixes 0.
