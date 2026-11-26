# Components of the first full-product presentation arrow

Let C be an abelian category with object universe u and morphism universe v. Let P be an
integer-indexed chain complex. Put Bₚ=im(d_P : Pₚ₊₁ → Pₚ), Zₚ=Zₚ(P), and Hₚ=Hₚ(P), with boundary
inclusion βₚ : Bₚ → Zₚ and quotient πₚ : Zₚ → Hₚ. Let Y : ℤ → C be a coefficient family and
assume Ext_C is available in universe w. The full presentation has terms ∏ₚ Hom_C(Zₚ,Yₚ) → ∏ₚ
Hom_C(Bₚ,Yₚ) → ∏ₚ Ext¹_C(Hₚ,Yₚ), in the common group universe max(v,w). The first arrow sends a
family (tₚ : Zₚ → Yₚ) to (tₚ ∘ βₚ : Bₚ → Yₚ), with the canonical lifts of these Hom groups.
