/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantGradedPieceNaturalMap

/-! # Tests for the natural-stage graded-piece projection -/

@[expose] public section

open CategoryTheory Limits CategoryTheory.Pretriangulated

noncomputable section

universe v u

namespace HomologicalComplex₂.FirstQuadrantGradedPieceNaturalMapTests

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

example (p : ℕ) :
    (horizontalFilteredTotalComplex K p).extend
        ComplexShape.embeddingDownNat ⟶
      horizontalDirectColumnCochain K p :=
  horizontalNaturalDirectColumnProjectionMap K p

example (p : ℕ) :
    (ComplexShape.embeddingDownNat.extendFunctor C).map
        (horizontalFilteredTotalComplexMap K (Nat.le_succ p)) ≫
      horizontalNaturalDirectColumnProjectionMap K (p + 1) = 0 :=
  horizontalNaturalDirectColumnProjectionMap_stageMap_zero K p

end HomologicalComplex₂.FirstQuadrantGradedPieceNaturalMapTests

end
