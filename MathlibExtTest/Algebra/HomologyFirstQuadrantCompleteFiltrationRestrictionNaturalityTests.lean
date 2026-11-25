/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltrationRestrictionNaturality

/-! # Tests for bicomplex naturality of complete-filtration restriction -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace HomologicalComplex₂.FirstQuadrantCompleteFiltrationRestrictionNaturalityTests

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

#check horizontalCompleteTotalFiltrationNatRestrictionDiagramFunctor
#check horizontalTotalFiltrationDiagramFunctor
#check horizontalCompleteTotalFiltrationNatRestrictionDiagramFunctor_obj
#check horizontalCompleteTotalFiltrationNatRestrictionDiagramFunctor_map_app
#check horizontalTotalFiltrationDiagramFunctor_obj
#check horizontalTotalFiltrationDiagramFunctor_map_app
#check horizontalCompleteTotalFiltrationNatRestrictionNatIso
#check horizontalCompleteTotalFiltrationNatRestrictionNatIso_hom_app
#check horizontalCompleteTotalFiltrationNatRestrictionNatIso_hom_app_app

example :
    HomologicalComplex₂ C (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) ⥤
      (ℕ ⥤ ChainComplex C ℕ) :=
  horizontalCompleteTotalFiltrationNatRestrictionDiagramFunctor

example :
    horizontalCompleteTotalFiltrationNatRestrictionDiagramFunctor (C := C) ≅
      horizontalTotalFiltrationDiagramFunctor (C := C) :=
  horizontalCompleteTotalFiltrationNatRestrictionNatIso

example (f : K ⟶ L) (n : ℕ) :
    (horizontalCompleteTotalFiltrationNatRestrictionDiagramFunctor.map f).app n =
      horizontalCompleteFilteredTotalComplexMapOfBicomplex f
        ((n : ℤ) : EInt) :=
  horizontalCompleteTotalFiltrationNatRestrictionDiagramFunctor_map_app f n

example (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)) (n : ℕ) :
    ((horizontalCompleteTotalFiltrationNatRestrictionNatIso
      (C := C)).hom.app K).app n =
        (horizontalCompleteFilteredTotalComplexFiniteIso K
          (n : ℤ) (Int.natCast_nonneg n)).hom :=
  horizontalCompleteTotalFiltrationNatRestrictionNatIso_hom_app_app K n

#print axioms horizontalCompleteTotalFiltrationNatRestrictionDiagramFunctor
#print axioms horizontalTotalFiltrationDiagramFunctor
#print axioms horizontalCompleteTotalFiltrationNatRestrictionNatIso
#print axioms horizontalCompleteTotalFiltrationNatRestrictionNatIso_hom_app
#print axioms horizontalCompleteTotalFiltrationNatRestrictionNatIso_hom_app_app

end HomologicalComplex₂.FirstQuadrantCompleteFiltrationRestrictionNaturalityTests

end
