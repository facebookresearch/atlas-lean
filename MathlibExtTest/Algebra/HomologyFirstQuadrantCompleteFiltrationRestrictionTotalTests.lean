/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltrationRestrictionTotal

/-! # Tests for total compatibility of complete-filtration restriction -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace HomologicalComplex₂.FirstQuadrantCompleteFiltrationRestrictionTotalTests

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

#check horizontalTotalComplexNatConstDiagramFunctor
#check horizontalTotalComplexNatConstDiagramFunctor_obj
#check horizontalTotalComplexNatConstDiagramFunctor_map_app
#check horizontalTotalFiltrationDiagramToTotal
#check horizontalTotalFiltrationDiagramToTotal_app
#check horizontalTotalFiltrationDiagramToTotal_app_app
#check horizontalCompleteTotalFiltrationNatRestrictionDiagramToTotal
#check horizontalCompleteTotalFiltrationNatRestrictionDiagramToTotal_app
#check horizontalCompleteTotalFiltrationNatRestrictionDiagramToTotal_app_app
#check horizontalCompleteTotalFiltrationNatRestrictionNatIso_hom_comp_toTotal

example :
    horizontalTotalFiltrationDiagramFunctor (C := C) ⟶
      horizontalTotalComplexNatConstDiagramFunctor (C := C) :=
  horizontalTotalFiltrationDiagramToTotal

example :
    horizontalCompleteTotalFiltrationNatRestrictionDiagramFunctor (C := C) ⟶
      horizontalTotalComplexNatConstDiagramFunctor (C := C) :=
  horizontalCompleteTotalFiltrationNatRestrictionDiagramToTotal

example :
    (horizontalCompleteTotalFiltrationNatRestrictionNatIso
        (C := C)).hom ≫
      horizontalTotalFiltrationDiagramToTotal (C := C) =
    horizontalCompleteTotalFiltrationNatRestrictionDiagramToTotal
      (C := C) :=
  horizontalCompleteTotalFiltrationNatRestrictionNatIso_hom_comp_toTotal

example (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)) (n : ℕ) :
    ((horizontalCompleteTotalFiltrationNatRestrictionDiagramToTotal
      (C := C)).app K).app n =
        horizontalCompleteFilteredTotalToTotal K ((n : ℤ) : EInt) :=
  horizontalCompleteTotalFiltrationNatRestrictionDiagramToTotal_app_app K n

#print axioms horizontalTotalComplexNatConstDiagramFunctor
#print axioms horizontalTotalFiltrationDiagramToTotal
#print axioms horizontalCompleteTotalFiltrationNatRestrictionDiagramToTotal
#print axioms horizontalCompleteTotalFiltrationNatRestrictionNatIso_hom_comp_toTotal

end HomologicalComplex₂.FirstQuadrantCompleteFiltrationRestrictionTotalTests

end
