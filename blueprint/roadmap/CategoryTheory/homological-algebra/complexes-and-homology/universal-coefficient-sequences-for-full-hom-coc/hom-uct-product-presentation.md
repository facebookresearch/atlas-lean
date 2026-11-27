# The full product Hom–Ext presentation

Let C be an abelian category with object universe u and morphism universe v. Let P be an
integer-indexed chain complex. Put Bₚ=im(d_P : Pₚ₊₁ → Pₚ), Zₚ=Zₚ(P), and Hₚ=Hₚ(P), with boundary
inclusion βₚ : Bₚ → Zₚ and quotient πₚ : Zₚ → Hₚ. Let Y : ℤ → C be a coefficient family and
assume Ext_C is available in universe w. The full presentation has terms ∏ₚ Hom_C(Zₚ,Yₚ) → ∏ₚ
Hom_C(Bₚ,Yₚ) → ∏ₚ Ext¹_C(Hₚ,Yₚ), in the common group universe max(v,w). The product short
complex uses precomposition with βₚ in its first arrow and tₚ ↦ (tₚ)_*[0 → Bₚ → Zₚ → Hₚ → 0] in
its second arrow, in each integer coordinate.
