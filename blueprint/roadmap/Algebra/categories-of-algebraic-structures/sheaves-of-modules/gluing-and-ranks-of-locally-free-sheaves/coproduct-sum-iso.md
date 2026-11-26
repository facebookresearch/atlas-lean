# Coproduct of a sum-indexed family

Let `D` be any category, with families `f₁ : ι₁ → D` and `f₂ : ι₂ → D` whose index universes
may differ. Assume the coproducts of `f₁`, `f₂`, and `Sum.elim f₁ f₂` exist, and that the
binary coproduct of `∐ f₁` and `∐ f₂` exists. Then there is a canonical isomorphism `∐
(Sum.elim f₁ f₂) ≅ (∐ f₁) ⨿ (∐ f₂)`.
