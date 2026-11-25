/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalLowerComparisonCocone
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.LowerSetColimits
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.LowerRestriction
public import Mathlib.CategoryTheory.Limits.IsLimit
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Basic

/-!
# Actual natural comparisons and lower UPs of original lower restrictions

The original cell tree and its actual chosen lower colimits construct
natural comparisons on every literal original lower subset. Its full original
lower universal properties are whiskered along the identity on original
labels. Empty original prefixes are good with the original arbitrary root.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w t u v

namespace CategoryTheory.SmallObject.OriginalLowerRestrictionComparison

open Limits LowerSetColimits

variable {C : Type u} [Category.{v} C] {P : Type w} [PartialOrder P]
  {A : Type t} {s : A → Arrow C} {X : C}
  (O : CellTree s X (P := P)) (M : LowerSetColimitData O.diagram)

/-- The original restricted prefix has its same literal original label order map. -/
def labels (S : LowerSet P) : S →o P where
  toFun := Subtype.val
  monotone' _ _ h := h

/-- The original lower preimage has the same entire actual original lower-label carrier. -/
def carrierIso (S D : LowerSet P) (hD : D ≤ S) :
    OriginalLowerComparisonCocone.carrier (labels S) D ≃o D where
  toFun p := ⟨p.1.1, p.2⟩
  invFun p := ⟨⟨p.1, hD p.2⟩, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- The complete original restricted vertex comparison is its actual identity natural map. -/
abbrev comparison (S : LowerSet P) :
    (CellTreeLowerRestriction.tree O M S).diagram ⟶ (labels S).monotone.functor ⋙ O.diagram :=
  𝟙 (CellTreeLowerRestriction.tree O M S).diagram

/-- Every actual original whole lower UP is retained inside its same original restricted prefix. -/
def lowerIsColimit (S D : LowerSet P) (hD : D ≤ S) :
    IsColimit (OriginalLowerComparisonCocone.cocone (labels S)
      (CellTreeLowerRestriction.tree O M S).diagram O.diagram (comparison O M S) M D) := by
  apply IsColimit.ofIsoColimit ((M.isColimit D).whiskerEquivalence (carrierIso S D hD).equivalence)
  exact Cocone.ext (Iso.refl _) (fun p => by
    change M.ι D ((carrierIso S D hD) p) ≫ 𝟙 _ =
      𝟙 _ ≫ M.ι D ⟨p.1.1, p.2⟩
    rw [Category.comp_id, Category.id_comp]
    rfl)

end CategoryTheory.SmallObject.OriginalLowerRestrictionComparison
