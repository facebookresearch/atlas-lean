/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uV vV

open CategoryTheory CategoryTheory.MonoidalCategory
  CategoryTheory.MonoidalOpposite
open scoped CategoryTheory.Prod

namespace CategoryTheory.Enriched.SphereOperator

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V]

/-- The literal inverse mixed crossing and positive coefficient crossing satisfy
the complete triple tensorator coherence, with the coefficient order reversed.
The monoidal structure used in the proof is derived from the stock tensor and
monoidal-opposite functors; it is not an additional hypothesis. -/
theorem tensorDelta_ordered_triple (W Z T A B C : V) :
    ((tensorδ W Z A B ≫
        (𝟙 (W ⊗ Z) ⊗ₘ (β_ A B).hom)) ▷ (T ⊗ C)) ≫
        (tensorδ (W ⊗ Z) T (B ⊗ A) C ≫
          (𝟙 ((W ⊗ Z) ⊗ T) ⊗ₘ (β_ (B ⊗ A) C).hom)) ≫
        ((α_ W Z T).hom ⊗ₘ (α_ C B A).inv) =
      (α_ (W ⊗ A) (Z ⊗ B) (T ⊗ C)).hom ≫
        ((W ⊗ A) ◁ (tensorδ Z T B C ≫
          (𝟙 (Z ⊗ T) ⊗ₘ (β_ B C).hom))) ≫
        (tensorδ W (Z ⊗ T) A (C ⊗ B) ≫
          (𝟙 (W ⊗ (Z ⊗ T)) ⊗ₘ (β_ A (C ⊗ B)).hom)) := by
  -- Capture both the literal original crossing and the original positive
  -- monoidal-opposite tensorator before deriving the reversed braiding.
  let Φ : ∀ W Z A B : V,
      (W ⊗ A) ⊗ (Z ⊗ B) ⟶ (W ⊗ Z) ⊗ (B ⊗ A) :=
    fun W Z A B => tensorδ W Z A B ≫
      (𝟙 (W ⊗ Z) ⊗ₘ (β_ A B).hom)
  have hCoherence :
      ((Φ W Z A B) ▷ (T ⊗ C)) ≫ Φ (W ⊗ Z) T (B ⊗ A) C ≫
          ((α_ W Z T).hom ⊗ₘ (α_ C B A).inv) =
        (α_ (W ⊗ A) (Z ⊗ B) (T ⊗ C)).hom ≫
          ((W ⊗ A) ◁ Φ Z T B C) ≫ Φ W (Z ⊗ T) A (C ⊗ B) := by
    let F₀ : V × Vᴹᵒᵖ ⥤ V × V :=
      Functor.prod (𝟭 V) (unmopFunctor V)
    let hF₀ : F₀.LaxMonoidal := inferInstance
    let : BraidedCategory V := reverseBraiding V
    let : F₀.LaxMonoidal := hF₀
    let F : V × Vᴹᵒᵖ ⥤ V := F₀ ⋙ MonoidalCategory.tensor V
    let : F.LaxMonoidal := inferInstance
    -- These equations retain all six objects and both tensor factors. The
    -- tensor functor with reversed braiding has the original tensorδ as μ.
    have hTensorator (W Z A B : V) :
        Functor.LaxMonoidal.μ F (W, mop A) (Z, mop B) = Φ W Z A B := by
      rfl
    have hAssociator :
        F.map (α_ (W, mop A) (Z, mop B) (T, mop C)).hom =
          ((α_ W Z T).hom ⊗ₘ (α_ C B A).inv) := by
      rfl
    have h := Functor.LaxMonoidal.associativity F
      (W, mop A) (Z, mop B) (T, mop C)
    change (Functor.LaxMonoidal.μ F (W, mop A) (Z, mop B) ▷ (T ⊗ C)) ≫
        Functor.LaxMonoidal.μ F (W ⊗ Z, mop (B ⊗ A)) (T, mop C) ≫
        F.map (α_ (W, mop A) (Z, mop B) (T, mop C)).hom =
      (α_ (W ⊗ A) (Z ⊗ B) (T ⊗ C)).hom ≫
        ((W ⊗ A) ◁ Functor.LaxMonoidal.μ F (Z, mop B) (T, mop C)) ≫
        Functor.LaxMonoidal.μ F (W, mop A) (Z ⊗ T, mop (C ⊗ B)) at h
    simp only [hTensorator, hAssociator] at h
    simpa only [F, F₀, Functor.comp_obj, Functor.prod_obj,
      MonoidalCategory.tensor_obj, Functor.id_obj,
      prodMonoidal_tensorObj, unmopFunctor, unmop_tensorObj] using h
  dsimp only [Φ] at hCoherence
  simp only [Category.assoc] at hCoherence ⊢
  exact hCoherence

end CategoryTheory.Enriched.SphereOperator
