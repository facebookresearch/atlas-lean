# Fixing the first cyclic input gives an alternating tail map

Let k be a commutative ring and A a possibly noncommutative ring with a k-algebra structure.
Let Cλ_n be degree n of its Connes cyclic quotient and q_n : A^⊗(n+1) →ₗ[k] Cλ_n the
whole-tensor quotient map. For n : ℕ, cyclicTailAlternating n : A →ₗ[k] Alt(Fin n, A; Cλ_n)
fixes the first input x and alternates the remaining n. Its value on a tail a is cyclicTailSum
n (Fin.cons x a).
