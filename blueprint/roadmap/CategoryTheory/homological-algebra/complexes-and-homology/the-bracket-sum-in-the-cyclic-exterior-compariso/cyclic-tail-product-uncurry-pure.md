# The double-uncurry formula has the signed two-deletion bracket sum

Let k be a commutative ring and A a possibly noncommutative ring with a k-algebra structure.
Let Cλ_n be degree n of its Connes cyclic quotient and q_n : A^⊗(n+1) →ₗ[k] Cλ_n the
whole-tensor quotient map. For a : Fin (n + 2) → A, cyclicTailProductUncurry n a = ∑ i :
Fin(n+1), ∑ j ≥ i, (−1 : ℤ)^(i.val+j.val) • cyclicTailSum n (Fin.cons
⁅a_(i.castSucc),a_(j.succ)⁆ (j.removeNth(i.castSucc.removeNth a))). The bracket is a_i*a_(j+1)
− a_(j+1)*a_i; the two removals occur in the displayed order.
