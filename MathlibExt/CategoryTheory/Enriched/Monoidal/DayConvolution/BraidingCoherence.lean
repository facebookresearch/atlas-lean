/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.Basic

/-!
# Full-Hom interchange for the Day input swap

The actual value symmetry interchanges both factors of the product-enriched
Hom and respects its full composition map.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uV vV uA uB
open CategoryTheory MonoidalCategory BraidedCategory

namespace CategoryTheory.EnrichedDayKernel.BraidingCoherence

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]

/-- Swapping the complete product-enriched Hom respects the actual middle interchange. -/
theorem tensorMu_swap (A B C D : V) :
    tensorμ A B C D ≫ (β_ (A ⊗ C) (B ⊗ D)).hom =
      ((β_ A B).hom ⊗ₘ (β_ C D).hom) ≫ tensorμ B A D C := by
  let t : (A ⊗ B) ⊗ (C ⊗ D) ⟶ (A ⊗ B) ⊗ (C ⊗ D) :=
    (α_ A B (C ⊗ D)).hom ≫ A ◁ (α_ B C D).inv ≫
      A ◁ (((β_ B C).hom ≫ (β_ C B).hom) ▷ D) ≫
      A ◁ (α_ B C D).hom ≫ (α_ A B (C ⊗ D)).inv
  have ht : t = 𝟙 ((A ⊗ B) ⊗ (C ⊗ D)) := by
    dsimp only [t]
    rw [SymmetricCategory.symmetry]
    simp only [id_whiskerRight, whiskerLeft_id, Category.id_comp]
    rw [← whiskerLeft_comp_assoc, Iso.inv_hom_id, whiskerLeft_id, Category.id_comp,
      Iso.hom_inv_id]
  calc
    _ = t ≫ ((β_ A B).hom ⊗ₘ (β_ C D).hom) ≫ tensorμ B A D C := by
      dsimp only [t, tensorμ]
      simp only [braiding_tensor_left_hom, braiding_tensor_right_hom,
        whiskerLeft_comp, comp_whiskerRight, Category.assoc]
      rw [tensorHom_def]
      monoidal
    _ = _ := by rw [ht, Category.id_comp]

end CategoryTheory.EnrichedDayKernel.BraidingCoherence
