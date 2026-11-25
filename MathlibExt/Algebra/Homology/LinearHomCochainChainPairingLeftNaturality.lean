/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.Algebra.Homology.LinearHomCochainChainPairingLeftTmulNaturality

@[expose] public section

open CategoryTheory MonoidalCategory
open scoped TensorProduct

universe u

namespace HomologicalComplex

/-- Naturality of `linearHomCochainChainPair` under a morphism
    of the left chain complex and compatible diagonals. -/
@[reassoc]
theorem linearHomCochainChainPair_naturality_left
    {R : Type u} [CommRing R] {A : ModuleCat.{u} R}
    {K₁ K₁' K₂ K₃ K₃' L : ChainComplex (ModuleCat.{u} R) ℕ}
    (Δ : K₃ ⟶ tensorObj K₁ K₂)
    (Δ' : K₃' ⟶ tensorObj K₁' K₂)
    (f₁ : K₁' ⟶ K₁) (f₃ : K₃' ⟶ K₃)
    (ρ : ∀ q, A ⊗ K₂.X q ⟶ L.X q)
    (hΔ : f₃ ≫ Δ = Δ' ≫ tensorHom f₁ (𝟙 K₂))
    (p q : ℕ) :
    (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).map f₁.op).f p ⊗ₘ
        𝟙 (K₃'.X (p + q))) ≫
      linearHomCochainChainPair R Δ' ρ p q =
    (𝟙 (ModuleCat.of R (K₁.X p ⟶ A)) ⊗ₘ f₃.f (p + q)) ≫
      linearHomCochainChainPair R Δ ρ p q := by
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro φ x
  have hL : ((((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).map
      f₁.op).f p ⊗ₘ 𝟙 (K₃'.X (p + q))).hom (φ ⊗ₜ[R] x)) =
      (f₁.f p ≫ φ) ⊗ₜ[R] x := by
    simp
    rfl
  have hR : ((𝟙 (ModuleCat.of R (K₁.X p ⟶ A)) ⊗ₘ f₃.f (p + q)).hom
      (φ ⊗ₜ[R] x)) = φ ⊗ₜ[R] (f₃.f (p + q)).hom x := by
    simp
    rfl
  change (linearHomCochainChainPair R Δ' ρ p q).hom
      ((((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).map f₁.op).f p ⊗ₘ
        𝟙 (K₃'.X (p + q))).hom (φ ⊗ₜ[R] x)) =
    (linearHomCochainChainPair R Δ ρ p q).hom
      ((𝟙 (ModuleCat.of R (K₁.X p ⟶ A)) ⊗ₘ f₃.f (p + q)).hom (φ ⊗ₜ[R] x))
  rw [hL, hR]
  exact linearHomCochainChainPair_naturality_left_tmul Δ Δ' f₁ f₃ ρ hΔ p q φ x

end HomologicalComplex

end
