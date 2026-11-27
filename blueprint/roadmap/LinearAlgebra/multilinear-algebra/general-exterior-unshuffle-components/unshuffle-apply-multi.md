# Unshuffle is the block-coset alternating sum

Let `R` be a commutative ring, `M` an `R`-module, `p,q : ℕ`, `v : Fin(p+q) → M`, and
`u=finSumFinEquiv`. Then `unshuffle R M p q (ιMulti_R v)` is the sum over `Perm.ModSumCongr
(Fin p) (Fin q)`. For a representative `σ` of a coset, the summand is `sign(σ) • (ιMulti_R(fun
i ↦ v(u(σ(Sum.inl i)))) ⊗ ιMulti_R(fun j ↦ v(u(σ(Sum.inr j)))))`.
