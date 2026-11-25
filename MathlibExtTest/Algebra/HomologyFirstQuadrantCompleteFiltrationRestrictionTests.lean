/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltrationRestriction

/-! # Tests for restriction of the complete filtration -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace HomologicalComplex₂.FirstQuadrantCompleteFiltrationRestrictionTests

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]

#check horizontalFiltrationNatToEIntOrderHom
#check horizontalFiltrationNatToEIntOrderHom_apply
#check horizontalFiltrationNatToEIntFunctor
#check horizontalFiltrationNatToEIntFunctor_obj
#check horizontalFiltrationNatToEIntFunctor_map
#check horizontalCompleteTotalFiltrationNatRestrictionIso
#check horizontalCompleteTotalFiltrationNatRestrictionIso_hom_app
#check horizontalCompleteTotalFiltrationNatRestrictionIso_hom_comp_ι

example : ℕ ⥤ EInt :=
  horizontalFiltrationNatToEIntFunctor

example (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)) :
    horizontalFiltrationNatToEIntFunctor ⋙
        (horizontalCompleteTotalFiltration K).diagram ≅
      (horizontalTotalFiltration K).diagram :=
  horizontalCompleteTotalFiltrationNatRestrictionIso K

example (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)) :
    (horizontalCompleteTotalFiltrationNatRestrictionIso K).hom ≫
        (horizontalTotalFiltration K).ι =
      Functor.whiskerLeft horizontalFiltrationNatToEIntFunctor
        (horizontalCompleteTotalFiltration K).ι :=
  horizontalCompleteTotalFiltrationNatRestrictionIso_hom_comp_ι K

#print axioms horizontalFiltrationNatToEIntOrderHom
#print axioms horizontalCompleteTotalFiltrationNatRestrictionIso
#print axioms horizontalCompleteTotalFiltrationNatRestrictionIso_hom_app
#print axioms horizontalCompleteTotalFiltrationNatRestrictionIso_hom_comp_ι

end HomologicalComplex₂.FirstQuadrantCompleteFiltrationRestrictionTests

end
