/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFirstPageZeroBoundary

/-! # Tests for the column-one to column-zero first-page boundary -/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂.FirstQuadrantFirstPageZeroBoundaryTests

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

example :
    (horizontalCompleteFilteredTotalMonoOverUpperIso K 0).symm ≪≫
      horizontalCompleteFilteredTotalMonoOverMiddleIso K 0 ≪≫
      horizontalCompleteFilteredTotalMonoOverLowerSuccIso K 0 =
    Iso.refl _ :=
  horizontalCompleteFilteredTotalMonoOver_zero_middle_triangle K

example :
    (horizontalCompleteFiltrationCochainUpperIso K 0).inv ≫
      (horizontalFirstPageMiddleStageIso K 0).hom ≫
      (horizontalCompleteFiltrationCochainMonoLowerSuccIso K 0).hom ≫
      (horizontalNaturalStageCochainIso K 0).hom =
    𝟙 _ :=
  horizontalFirstPageZeroMiddleStageTriangle K

example (q : ℕ) :
    (horizontalDirectColumnCochain K (0 + 1)).iCycles
        (-((0 + 1 : ℕ) : ℤ) - q) ≫
      horizontalCompleteSuccDirectColumnSection K 0 q ≫
      ((horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageUpperIndex (0 + 1))).d
          (-((0 + 1 : ℕ) : ℤ) - q) (-((0 : ℕ) : ℤ) - q) =
    (horizontalDirectColumnCochain K (0 + 1)).iCycles
        (-((0 + 1 : ℕ) : ℤ) - q) ≫
      (horizontalDirectColumnCochainXIso K (0 + 1) q).hom ≫
      (K.d (0 + 1) 0).f q ≫
      (horizontalDirectColumnCochainXIso K 0 q).inv ≫
      horizontalCompleteDirectColumnSectionComponent K 0 q ≫
      (horizontalFirstPageNextFiltrationMap K 0).f
        (-((0 : ℕ) : ℤ) - q) :=
  horizontalCompleteOneToZeroDirectColumnSection_d K q

end HomologicalComplex₂.FirstQuadrantFirstPageZeroBoundaryTests

end
