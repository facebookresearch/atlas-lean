/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-! # Whole product mates of an actual adjunction

The canonical left product comparison is read by the same adjunction as
the product of both original Hom mates followed by the inverse right
product comparison. No comparison isomorphism for the left functor is
assumed or constructed.
-/

noncomputable section
universe uC vC uD vD
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Adjunction

variable {C : Type uC} [Category.{vC} C] [HasBinaryProducts C]
  {D : Type uD} [Category.{vD} D] [HasBinaryProducts D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)

/-- The right adjoint retains the canonical whole product isomorphism. -/
def rightProductIso (A B : D) : R.obj (A ⨯ B) ≅ R.obj A ⨯ R.obj B := by
  let _ : R.IsRightAdjoint := adj.isRightAdjoint
  exact asIso (Limits.prodComparison R A B)

/-- The original product comparison is the forward map of the genuine right product Iso. -/
theorem rightProductIso_hom (A B : D) :
    (rightProductIso adj A B).hom = Limits.prodComparison R A B := rfl

/-- Product of original mate maps, including the entire original right product comparison. -/
theorem homEquiv_product {X Y : C} {A B : D}
    (f : L.obj X ⟶ A) (g : L.obj Y ⟶ B) :
    adj.homEquiv (X ⨯ Y) (A ⨯ B)
      (Limits.prodComparison L X Y ≫ prod.map f g) =
        prod.map (adj.homEquiv X A f) (adj.homEquiv Y B g) ≫
          (rightProductIso adj A B).inv := by
  apply (cancel_mono (rightProductIso adj A B).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply prod.hom_ext
  · rw [Category.assoc, rightProductIso_hom]
    rw [prodComparison_fst, ← adj.homEquiv_naturality_right]
    rw [Category.assoc, prod.map_fst, ← Category.assoc, prodComparison_fst,
      adj.homEquiv_naturality_left, prod.map_fst]
  · rw [Category.assoc, rightProductIso_hom]
    rw [prodComparison_snd, ← adj.homEquiv_naturality_right]
    rw [Category.assoc, prod.map_snd, ← Category.assoc, prodComparison_snd,
      adj.homEquiv_naturality_left, prod.map_snd]

end CategoryTheory.Adjunction
