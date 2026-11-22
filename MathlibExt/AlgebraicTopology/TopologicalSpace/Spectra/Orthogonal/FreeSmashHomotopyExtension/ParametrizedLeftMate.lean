/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Adjunction.OriginalParametrizedParameter
import MathlibExt.CategoryTheory.Adjunction.OriginalParametrizedPostcomposition
import MathlibExt.CategoryTheory.Adjunction.ParametrizedLeftIsoComparison
import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Parametrized adjunction mates and coefficient naturality

A parametrized adjunction and an ordinary adjunction transport a supplied right-hand
internal-Hom comparison to an isomorphism of the left-hand functors. The resulting mate is
natural in the coefficient, with the formula retaining the given right comparison and both
adjunctions.
-/

set_option autoImplicit false
noncomputable section
universe uV vV uC vC
open CategoryTheory MonoidalCategory

namespace OrthogonalIGeneratorProbe.ParametrizedMate

variable {V : Type uV} [Category.{vV} V]
  {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [MonoidalClosed C]

/-- Whole actual coefficient naturality of a right comparison determines the original left mate. -/
def comparison (F : V ⥤ C) {S : V ⥤ C ⥤ C} {T : Vᵒᵖ ⥤ C ⥤ C}
    (a : S ⊣₂ T) {L R : C ⥤ C} (b : L ⊣ R)
    (e : F.op ⋙ MonoidalClosed.internalHom ≅
      ParametrizedAdjunction.OriginalPostcomposition.right (G := T) (R := R)) :
    F ⋙ curriedTensor C ≅
      ParametrizedAdjunction.OriginalPostcomposition.left (F := S) (L := L) :=
  ParametrizedAdjunction.LeftIsoComparison.iso
    (ParametrizedAdjunction.OriginalParameter.adjunction
      MonoidalClosed.internalHomAdjunction₂ F)
    (ParametrizedAdjunction.OriginalPostcomposition.adjunction a b) e

/-- The full literal parameter arrow keeps both chosen comparison maps. -/
theorem coefficient_naturality (F : V ⥤ C) {S : V ⥤ C ⥤ C}
    {T : Vᵒᵖ ⥤ C ⥤ C} (a : S ⊣₂ T) {L R : C ⥤ C} (b : L ⊣ R)
    (e : F.op ⋙ MonoidalClosed.internalHom ≅
      ParametrizedAdjunction.OriginalPostcomposition.right (G := T) (R := R))
    {K K' : V} (i : K ⟶ K') (Y : C) :
    F.map i ▷ Y ≫ ((comparison F a b e).app K').hom.app Y =
      ((comparison F a b e).app K).hom.app Y ≫ L.map ((S.map i).app Y) := by
  exact congrArg (fun t => t.app Y) ((comparison F a b e).hom.naturality i)




end OrthogonalIGeneratorProbe.ParametrizedMate
