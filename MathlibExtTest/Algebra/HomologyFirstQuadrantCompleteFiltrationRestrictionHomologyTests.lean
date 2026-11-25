/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltrationRestrictionHomology

/-! # Tests for homology of complete-filtration restriction -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace HomologicalComplex₂.FirstQuadrantCompleteFiltrationRestrictionHomologyTests

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C] [CategoryWithHomology C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

#check horizontalNatDiagramHomologyFunctor
#check horizontalCompleteTotalFiltrationNatRestrictionHomologyDiagramFunctor
#check horizontalTotalFiltrationHomologyDiagramFunctor
#check horizontalTotalHomologyNatConstDiagramFunctor
#check horizontalCompleteTotalFiltrationNatRestrictionHomologyDiagramFunctor_obj_obj
#check horizontalTotalFiltrationHomologyDiagramFunctor_obj_obj
#check horizontalTotalHomologyNatConstDiagramFunctor_obj_obj
#check horizontalCompleteTotalFiltrationNatRestrictionHomologyDiagramFunctor_map_app
#check horizontalTotalFiltrationHomologyDiagramFunctor_map_app
#check horizontalTotalHomologyNatConstDiagramFunctor_map_app
#check horizontalCompleteTotalFiltrationNatRestrictionHomologyNatIso
#check horizontalCompleteTotalFiltrationNatRestrictionHomologyNatIso_hom_app_app
#check horizontalTotalFiltrationHomologyDiagramToTotal
#check horizontalTotalFiltrationHomologyDiagramToTotal_app_app
#check horizontalCompleteTotalFiltrationNatRestrictionHomologyDiagramToTotal
#check horizontalCompleteTotalFiltrationNatRestrictionHomologyDiagramToTotal_app_app
#check horizontalCompleteTotalFiltrationNatRestrictionHomologyNatIso_hom_comp_toTotal

example (n : ℕ) :
    horizontalCompleteTotalFiltrationNatRestrictionHomologyDiagramFunctor
        (C := C) n ≅
      horizontalTotalFiltrationHomologyDiagramFunctor (C := C) n :=
  horizontalCompleteTotalFiltrationNatRestrictionHomologyNatIso n

example (n : ℕ) :
    (horizontalCompleteTotalFiltrationNatRestrictionHomologyNatIso
        (C := C) n).hom ≫
        horizontalTotalFiltrationHomologyDiagramToTotal (C := C) n =
      horizontalCompleteTotalFiltrationNatRestrictionHomologyDiagramToTotal
        (C := C) n :=
  horizontalCompleteTotalFiltrationNatRestrictionHomologyNatIso_hom_comp_toTotal n

example (n i : ℕ) (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)) :
    ((horizontalCompleteTotalFiltrationNatRestrictionHomologyNatIso
      (C := C) n).hom.app K).app i =
        HomologicalComplex.homologyMap
          (horizontalCompleteFilteredTotalComplexFiniteIso K
            (i : ℤ) (Int.natCast_nonneg i)).hom n :=
  horizontalCompleteTotalFiltrationNatRestrictionHomologyNatIso_hom_app_app
    n K i

#print axioms horizontalNatDiagramHomologyFunctor
#print axioms horizontalCompleteTotalFiltrationNatRestrictionHomologyDiagramFunctor
#print axioms horizontalCompleteTotalFiltrationNatRestrictionHomologyNatIso
#print axioms horizontalTotalFiltrationHomologyDiagramToTotal
#print axioms horizontalCompleteTotalFiltrationNatRestrictionHomologyDiagramToTotal
#print axioms horizontalCompleteTotalFiltrationNatRestrictionHomologyNatIso_hom_comp_toTotal

end HomologicalComplex₂.FirstQuadrantCompleteFiltrationRestrictionHomologyTests

end
