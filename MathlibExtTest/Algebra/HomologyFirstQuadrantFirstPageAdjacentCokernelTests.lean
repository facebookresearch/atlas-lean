/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFirstPageAdjacentCokernel

/-! # Tests for adjacent horizontal filtration quotients -/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂.FirstQuadrantFirstPageAdjacentCokernelTests

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

example (p : ℕ) :
    horizontalFirstPageUpperIndex p ≤
      horizontalFirstPageUpperIndex (p + 1) :=
  horizontalFirstPageUpperIndex_le_succ p

example (p : ℕ) :
    Mono (horizontalFirstPageNextFiltrationMap K p) := inferInstance

example (p : ℕ) :
    horizontalFirstPageNextFiltrationMap K p =
      (horizontalFirstPageMiddleStageIso K p).hom ≫
        horizontalFirstPageFiltrationMap K (p + 1) :=
  horizontalFirstPageNextFiltrationMap_eq_middle K p

example (p : ℕ) :
    (horizontalCompleteFilteredTotalMonoOverUpperSuccIso K p).symm ≪≫
      horizontalCompleteFilteredTotalMonoOverMiddleIso K (p + 1) ≪≫
      horizontalCompleteFilteredTotalMonoOverLowerSuccIso K (p + 1) =
    Iso.refl _ :=
  horizontalCompleteFilteredTotalMonoOver_middle_triangle K p

example (p : ℕ) (i : ℤ) :
    (horizontalCompleteFiltrationCochainMonoUpperSuccIso K p).inv.f i ≫
      (horizontalFirstPageMiddleStageIso K (p + 1)).hom.f i ≫
      (horizontalCompleteFiltrationCochainMonoLowerSuccIso K (p + 1)).hom.f i =
    𝟙 _ :=
  horizontalFirstPageMiddleStageTriangle_f K p i

example (p : ℕ) :
    (horizontalFirstPageAdjacentCokernelShortComplex K p).ShortExact :=
  horizontalFirstPageAdjacentCokernelShortExact K p

example (p : ℕ) :
    (horizontalFirstPageAdjacentCokernelShortComplex K p).X₁ ≅
      horizontalDirectColumnCochain K p :=
  horizontalFirstPageAdjacentLeftIso K p

example (p : ℕ) :
    (horizontalFirstPageAdjacentCokernelShortComplex K p).X₃ ≅
      horizontalDirectColumnCochain K (p + 1) :=
  horizontalFirstPageAdjacentRightIso K p

example (p : ℕ) :
    (horizontalFirstPageAdjacentDirectShortComplex K p).ShortExact :=
  horizontalFirstPageAdjacentDirectShortExact K p

end HomologicalComplex₂.FirstQuadrantFirstPageAdjacentCokernelTests

end
