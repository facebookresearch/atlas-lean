/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantGradedPieceCokernel

/-! # Tests for consecutive horizontal filtration stages -/

@[expose] public section

open CategoryTheory Limits CategoryTheory.Pretriangulated

noncomputable section

universe v u

namespace HomologicalComplex₂.FirstQuadrantGradedPieceCokernelTests

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

example (p : ℕ) :
    (horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageLowerIndex p) ⟶
      (horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageUpperIndex p) :=
  horizontalFirstPageFiltrationMap K p

example : horizontalFirstPageFiltrationMap K 0 ≫
    horizontalDirectColumnProjectionMap K 0 = 0 :=
  horizontalFirstPageFiltrationMap_zero_projection K

example (p : ℕ) :
    horizontalCompleteFilteredTotalMonoOverMap K
        (horizontalFirstPageIndex_le (p + 1)) ≫
        (horizontalCompleteFilteredTotalMonoOverUpperSuccIso K p).hom =
      (horizontalCompleteFilteredTotalMonoOverLowerSuccIso K p).hom ≫
        (horizontalTotalFiltration K).toMonoOver.map
          (homOfLE (Nat.le_succ p)) :=
  horizontalCompleteFilteredTotalMonoOverMap_succ K p

example (p : ℕ) :
    horizontalFirstPageFiltrationMap K (p + 1) ≫
        (horizontalCompleteFiltrationCochainMonoUpperSuccIso K p).hom =
      (horizontalCompleteFiltrationCochainMonoLowerSuccIso K p).hom ≫
        (ComplexShape.embeddingDownNat.extendFunctor C).map
          ((horizontalTotalFiltration K).toMonoOver.map
            (homOfLE (Nat.le_succ p))).hom.left :=
  horizontalFirstPageFiltrationMap_succ_monoIso K p

end HomologicalComplex₂.FirstQuadrantGradedPieceCokernelTests

end
