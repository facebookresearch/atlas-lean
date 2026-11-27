# The full tensor includes every signed permutation in its ordered coordinates

Let k be a commutative ring and A a k-algebra ring. Write π_n : A ⊗[k] TensorPower k n A →
Cλ_n for the Connes projection and Ω_n(a) for cyclicFullTensor k A n a. For a : Fin (n + 1) →
A, Ω_n(a) = ∑ σ : Perm(Fin(n+1)), sign(σ) • (a_(σ 0) ⊗ tprod(j ↦ a_(σ(j.succ)))). The first
tensor factor is the permuted zero entry and the tail uses the remaining permuted positions.
