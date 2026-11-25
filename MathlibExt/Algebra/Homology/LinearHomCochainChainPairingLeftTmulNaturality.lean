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

public import MathlibExt.Algebra.Homology.LinearHomCochainChainPairingLeftDescNaturality

@[expose] public section

open CategoryTheory MonoidalCategory
open scoped TensorProduct

universe u

namespace HomologicalComplex

/-- Left-variable naturality on pure tensors: precomposing the cochain with `f₁`
    matches pushing the chain argument forward along `f₃` under `f₃ ≫ Δ = Δ' ≫ tensorHom f₁ 𝟙`. -/
theorem linearHomCochainChainPair_naturality_left_tmul
    {R : Type u} [CommRing R] {A : ModuleCat.{u} R}
    {K₁ K₁' K₂ K₃ K₃' L : ChainComplex (ModuleCat.{u} R) ℕ}
    (Δ : K₃ ⟶ tensorObj K₁ K₂)
    (Δ' : K₃' ⟶ tensorObj K₁' K₂)
    (f₁ : K₁' ⟶ K₁) (f₃ : K₃' ⟶ K₃)
    (ρ : ∀ q, A ⊗ K₂.X q ⟶ L.X q)
    (hΔ : f₃ ≫ Δ = Δ' ≫ tensorHom f₁ (𝟙 K₂))
    (p q : ℕ) (φ : K₁.X p ⟶ A) (x : K₃'.X (p + q)) :
    (linearHomCochainChainPair R Δ' ρ p q).hom
        ((f₁.f p ≫ φ) ⊗ₜ[R] x) =
      (linearHomCochainChainPair R Δ ρ p q).hom
        (φ ⊗ₜ[R] (f₃.f (p + q)).hom x) := by
  rw [linearHomCochainChainPair_tmul, linearHomCochainChainPair_tmul]
  have hDesc := linearHomCochainChainPairDesc_naturality_left f₁ ρ p q φ
  have hΔpq : f₃.f (p + q) ≫ Δ.f (p + q) =
      Δ'.f (p + q) ≫ (tensorHom f₁ (𝟙 K₂)).f (p + q) := by
    simpa using congrArg (fun g : K₃' ⟶ tensorObj K₁ K₂ => g.f (p + q)) hΔ
  calc (Δ'.f (p + q) ≫ linearHomCochainChainPairDesc R ρ p q
        (f₁.f p ≫ φ)).hom x
      = (Δ'.f (p + q) ≫ (tensorHom f₁ (𝟙 K₂)).f (p + q) ≫
        linearHomCochainChainPairDesc R ρ p q φ).hom x := by
        rw [← hDesc]
      _ = ((Δ'.f (p + q) ≫ (tensorHom f₁ (𝟙 K₂)).f (p + q)) ≫
        linearHomCochainChainPairDesc R ρ p q φ).hom x := by
        rw [← Category.assoc]
      _ = ((f₃.f (p + q) ≫ Δ.f (p + q)) ≫
        linearHomCochainChainPairDesc R ρ p q φ).hom x := by
        rw [← hΔpq]
      _ = (f₃.f (p + q) ≫ Δ.f (p + q) ≫
        linearHomCochainChainPairDesc R ρ p q φ).hom x := by
        rw [Category.assoc]
      _ = (Δ.f (p + q) ≫ linearHomCochainChainPairDesc R ρ p q φ).hom
        ((f₃.f (p + q)).hom x) := rfl

end HomologicalComplex

end
