# The cyclic tail sum fixes the first input and alternates the rest

Let k be a commutative ring and A a possibly noncommutative ring with a k-algebra structure.
Let Cλ_n be degree n of its Connes cyclic quotient and q_n : A^⊗(n+1) →ₗ[k] Cλ_n the
whole-tensor quotient map. For a : Fin (n + 1) → A, cyclicTailSum n a is ∑ σ : Perm(Fin n),
sign(σ) • [a₀ ⊗ tprod(j ↦ a_((σ j).succ))] in Cλ_n. Only the last n inputs are permuted in
this formula.
