/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFirstPageCompleteBoundary

/-! # Tests for the complete-stage horizontal first-page boundary -/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂.FirstQuadrantFirstPageCompleteBoundaryTests

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

example (p q : ℕ) :
    (horizontalDirectColumnCochain K (p + 1)).iCycles
        (-((p + 1 : ℕ) : ℤ) - q) ≫
      (horizontalDirectColumnCochainXIso K (p + 1) q).hom ≫
      horizontalFilteredTopInclusionComplex K (p + 1) q ≫
      horizontalFilteredTotalDComplex K (p + 1) (p + 1 + q) (p + q) =
    (horizontalDirectColumnCochain K (p + 1)).iCycles
        (-((p + 1 : ℕ) : ℤ) - q) ≫
      (horizontalDirectColumnCochainXIso K (p + 1) q).hom ≫
      (K.d (p + 1) p).f q ≫
      horizontalFilteredPreviousColumnInclusionComplex K p q :=
  horizontalDirectColumnTopInclusionComplex_d_eq_previous K p q

example (p q : ℕ) :
    (horizontalDirectColumnCochainXIso K (p + 1) q).inv ≫
      horizontalCompleteSuccDirectColumnSection K p q ≫
      (horizontalFirstPageNextFiltrationMap K (p + 1)).f
        (-((p + 1 : ℕ) : ℤ) - q) =
    horizontalFilteredPreviousColumnInclusionComplex K (p + 1) q ≫
      ((horizontalFilteredTotalComplex K (p + 2)).extendXIso
        ComplexShape.embeddingDownNat
        (i := p + 1 + q) (i' := -((p + 1 : ℕ) : ℤ) - q)
        (by simp; omega)).inv ≫
      (horizontalNaturalStageCochainIso K (p + 2)).inv.f
        (-((p + 1 : ℕ) : ℤ) - q) ≫
      (horizontalCompleteFiltrationCochainMonoUpperSuccIso K (p + 1)).inv.f
        (-((p + 1 : ℕ) : ℤ) - q) :=
  horizontalCompleteSuccSection_nextMap_eq_filtered K p q

example (p q : ℕ) :
    (horizontalDirectColumnCochain K (p + 2)).iCycles
        (-((p + 2 : ℕ) : ℤ) - q) ≫
      horizontalCompleteSuccDirectColumnSection K (p + 1) q ≫
      ((horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageUpperIndex (p + 2))).d
          (-((p + 2 : ℕ) : ℤ) - q) (-((p + 1 : ℕ) : ℤ) - q) =
    (horizontalDirectColumnCochain K (p + 2)).iCycles
        (-((p + 2 : ℕ) : ℤ) - q) ≫
      (horizontalDirectColumnCochainXIso K (p + 2) q).hom ≫
      (K.d (p + 2) (p + 1)).f q ≫
      (horizontalDirectColumnCochainXIso K (p + 1) q).inv ≫
      horizontalCompleteSuccDirectColumnSection K p q ≫
      (horizontalFirstPageNextFiltrationMap K (p + 1)).f
        (-((p + 1 : ℕ) : ℤ) - q) :=
  horizontalCompleteSuccDirectColumnSection_d K p q

end HomologicalComplex₂.FirstQuadrantFirstPageCompleteBoundaryTests

end
