/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.Basic

/-!
# Braiding of the canonical closed self-enrichment

The canonical self-enriched tensor in a symmetric closed monoidal category
preserves the braiding on the whole internal-Hom objects.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uV vV

namespace CategoryTheory

open MonoidalCategory

variable (V : Type uV) [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V]

@[reassoc]
private theorem tensorμ_braiding (X Y A B : V) :
    tensorμ X Y A B ≫ (β_ (X ⊗ A) (Y ⊗ B)).hom =
      ((β_ X Y).hom ⊗ₘ (β_ A B).hom) ≫ tensorμ Y X B A := by
  simp [tensorμ, SymmetricCategory.braiding_swap_eq_inv_braiding A Y,
    tensorHom_def]

namespace MonoidalClosed

open scoped MonoidalClosed

variable [MonoidalClosed V]

private theorem selfTensorMap_braiding
    (X X' Y Y' : V) :
    curry (tensorμ X Y ((ihom X).obj X') ((ihom Y).obj Y') ≫
          ((ihom.ev X).app X' ⊗ₘ (ihom.ev Y).app Y')) ≫
        (ihom (X ⊗ Y)).map (β_ X' Y').hom =
      (β_ ((ihom X).obj X') ((ihom Y).obj Y')).hom ≫
        curry (tensorμ Y X ((ihom Y).obj Y') ((ihom X).obj X') ≫
          ((ihom.ev Y).app Y' ⊗ₘ (ihom.ev X).app X')) ≫
        (pre (β_ X Y).hom).app (Y' ⊗ X') := by
  have hp := curry_pre_app (β_ X Y).hom
    (tensorμ Y X ((ihom Y).obj Y') ((ihom X).obj X') ≫
      ((ihom.ev Y).app Y' ⊗ₘ (ihom.ev X).app X'))
  simp only [Functor.id_obj] at hp
  rw [← curry_natural_right, hp,
    ← curry_natural_left]
  apply uncurry_injective
  simp only [uncurry_curry, Category.assoc, Functor.id_obj]
  rw [BraidedCategory.braiding_naturality, tensorμ_braiding_assoc V]
  simp only [tensorHom_def', Category.assoc]

/-- The full internal-Hom tensor map intertwines source and target braidings. -/
public theorem enrichedMonoidalCategoryDataSelf_tensorMap_braiding
    (X X' Y Y' : V) :
    (enrichedMonoidalCategoryDataSelf V).tensorMap X X' Y Y' ≫
        (ihom (X ⊗ Y)).map (β_ X' Y').hom =
      (β_ ((ihom X).obj X') ((ihom Y).obj Y')).hom ≫
        (enrichedMonoidalCategoryDataSelf V).tensorMap Y Y' X X' ≫
        (pre (β_ X Y).hom).app (Y' ⊗ X') := by
  simpa only [enrichedMonoidalCategoryDataSelf_tensorMap,
    enrichedCategorySelf_hom] using selfTensorMap_braiding V X X' Y Y'

private theorem braidingUnitGradedNaturality_of_whisker
    {P Q R S H : V}
    (f : H ⟶ @EnrichedCategory.Hom V _ _ V
      (enrichedCategorySelf V) P Q)
    (g : H ⟶ @EnrichedCategory.Hom V _ _ V
      (enrichedCategorySelf V) R S)
    (a : P ⟶ R) (b : Q ⟶ S)
    (h : f ≫ eHomWhiskerLeft V P b =
      g ≫ eHomWhiskerRight V a S) :
    (β_ (𝟙_ V) H).hom ≫
          (f ⊗ₘ eHomEquiv V b) ≫ eComp V P Q S =
      (eHomEquiv V a ⊗ₘ g) ≫ eComp V P R S := by
  apply (cancel_epi (λ_ H).inv).1
  rw [leftUnitor_inv_braiding_assoc]
  rw [tensorHom_def_assoc]
  rw [← rightUnitor_inv_naturality_assoc]
  rw [tensorHom_def_assoc]
  rw [← whisker_exchange_assoc]
  rw [← leftUnitor_inv_naturality_assoc]
  simpa only [eHomWhiskerLeft, eHomWhiskerRight, Category.assoc] using h

/-- A symmetric closed monoidal category's canonical self-enrichment has the
genuine enriched naturality of its selected braiding. -/
public theorem enrichedBraidedMonoidalCategoryDataSelf :
    EnrichedBraidedMonoidalCategoryData V V
      (enrichedMonoidalCategoryDataSelf V) where
  braidingNaturality X X' Y Y' := by
    apply braidingUnitGradedNaturality_of_whisker V
    rw [enrichedOrdinaryCategorySelf_eHomWhiskerLeft,
      enrichedOrdinaryCategorySelf_eHomWhiskerRight]
    simpa only [Category.assoc, enrichedCategorySelf_hom] using
      enrichedMonoidalCategoryDataSelf_tensorMap_braiding V X X' Y Y'

end MonoidalClosed

end CategoryTheory
