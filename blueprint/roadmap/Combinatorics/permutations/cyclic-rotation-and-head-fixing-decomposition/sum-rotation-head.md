# Summing in rotation and fixed-head coordinates

Let `n : ℕ`, `N=n+1`, and `ρ=finRotate N`. Addition and negation on `Fin N` are taken modulo
`N`. For a commutative additive monoid `T` and `f : S_N → T`, `∑ σ ∈ S_N, f σ = ∑ r : Fin N, ∑
π ∈ S_n, f(ρ^r.val * headFixingHom n π)`.
