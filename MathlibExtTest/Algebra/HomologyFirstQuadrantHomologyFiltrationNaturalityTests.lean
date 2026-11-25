/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantHomologyFiltrationNaturality

/-! # Tests for naturality of the total-homology image filtration -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace HomologicalComplex₂.FirstQuadrantHomologyFiltrationNaturalityTests

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

#check horizontalFiniteHomologyToTotalSquareOfBicomplex
#check horizontalFiniteHomologyImageMapOfBicomplex
#check horizontalFiniteHomologyImageMapOfBicomplex_ι
#check horizontalFiniteHomologyOverDiagram
#check horizontalFiniteTotalHomologyFiltration
#check horizontalFiniteTotalHomologyFiltration_obj
#check horizontalFiniteTotalHomologyFiltration_ι_app
#check horizontalCompleteHomologyNatRestrictionOverDiagram
#check horizontalCompleteFiniteHomologyOverNatIso
#check horizontalCompleteFiniteHomologyImageMonoOverNatIso
#check horizontalCompleteFiniteHomologyFiltrationDiagramIso
#check horizontalCompleteFiniteHomologyFiltrationDiagramIso_hom_app
#check horizontalCompleteFiniteHomologyFiltrationDiagramIso_hom_ι

example (f : K ⟶ L) :
    image (HomologicalComplex.homologyMap
      (horizontalFilteredTotalComplexToTotal K 0) 0) ⟶
      image (HomologicalComplex.homologyMap
        (horizontalFilteredTotalComplexToTotal L 0) 0) :=
  horizontalFiniteHomologyImageMapOfBicomplex f 0 0

example (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)) :
    horizontalFiltrationNatToEIntFunctor ⋙
        (horizontalTotalHomologyFiltration K 0).diagram ≅
      (horizontalFiniteTotalHomologyFiltration K 0).diagram :=
  horizontalCompleteFiniteHomologyFiltrationDiagramIso K 0

example (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)) :
    (horizontalCompleteFiniteHomologyFiltrationDiagramIso K 0).hom.app 0 ≫
        (horizontalFiniteTotalHomologyFiltration K 0).ι.app 0 =
      (horizontalTotalHomologyFiltration K 0).ι.app
        (((0 : ℤ) : EInt)) :=
  horizontalCompleteFiniteHomologyFiltrationDiagramIso_hom_ι K 0 0

#print axioms horizontalFiniteHomologyImageMapOfBicomplex
#print axioms horizontalFiniteHomologyImageMapOfBicomplex_ι
#print axioms horizontalFiniteTotalHomologyFiltration
#print axioms horizontalCompleteFiniteHomologyOverNatIso
#print axioms horizontalCompleteFiniteHomologyFiltrationDiagramIso
#print axioms horizontalCompleteFiniteHomologyFiltrationDiagramIso_hom_ι

end HomologicalComplex₂.FirstQuadrantHomologyFiltrationNaturalityTests

end
