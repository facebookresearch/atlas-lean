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

public import MathlibExt.Algebra.Homology.LinearHomCochainChainPairing

@[expose] public section

open CategoryTheory MonoidalCategory HomologicalComplex

universe u

variable {R : Type u} [CommRing R]
variable {A : ModuleCat.{u} R}
variable {K₁ K₁' K₂ L : ChainComplex (ModuleCat.{u} R) ℕ}

/-- Naturality in the left chain-complex variable: precomposing the cochain with
  `f₁` agrees with pulling back the descriptor along `tensorHom f₁ 𝟙`. -/
theorem HomologicalComplex.linearHomCochainChainPairDesc_naturality_left
    (f₁ : K₁' ⟶ K₁) (ρ : ∀ q, A ⊗ K₂.X q ⟶ L.X q) (p q : ℕ)
    (φ : K₁.X p ⟶ A) :
    (HomologicalComplex.tensorHom f₁ (𝟙 K₂)).f (p + q) ≫
      HomologicalComplex.linearHomCochainChainPairDesc R ρ p q φ =
      HomologicalComplex.linearHomCochainChainPairDesc R ρ p q (f₁.f p ≫ φ) := by
  apply mapBifunctor.hom_ext
  intro i j h
  unfold HomologicalComplex.linearHomCochainChainPairDesc
  by_cases hi : i = p
  · subst i
    have hj : j = q := Nat.add_left_cancel h
    subst j
    simp only [← Category.assoc]
    simp only [ι_mapBifunctorDesc, dite_eq_left]
    simp only [Category.assoc]
    simp only [curriedTensor_obj_obj, ComplexShape.π_def, tensorHom_id,
      ι_mapBifunctorMap_assoc, id_f, curriedTensor_obj_map, ι_mapBifunctorDesc,
      ↓reduceDIte]
    rw [MonoidalCategory.comp_whiskerRight]
    simp
  · simp only [← Category.assoc]
    simp [hi]

end
