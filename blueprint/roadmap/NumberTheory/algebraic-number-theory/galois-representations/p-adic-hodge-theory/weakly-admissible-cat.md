# Weakly Admissible Cat

The category of finite-dimensional weakly admissible filtered `(φ, N)`-modules over `K`, for
a field `K₀` with a ring automorphism `σ` (with inverse `σ'`), a scalar `p ∈ K₀`, a field
extension `K` of `K₀` and an additive valuation `v : AddValuation K₀ (WithTop ℤ)`. An object is a
`K₀`-vector space `D` in the universe `u`, finite-dimensional over `K₀`, with a filtered
`(φ, N)`-module structure over `K` that is weakly admissible for `v`; the morphisms are the
morphisms of filtered `(φ, N)`-modules (`FilteredPhiNModule.Hom`). When `K` is a `p`-adic field,
`K₀ = W(k)[1/p]` is its maximal absolutely unramified subfield, `σ` is the absolute Frobenius and
`v` is the `p`-adic valuation (so `v ∘ σ = v`), this is the category `MF^ad_K(φ, N)` of
Fontaine–Ouyang, Definition 8.39 (who call these modules *admissible*), and the category of
Fontaine, Exposé III, §4.4.3, with `L = K`.
