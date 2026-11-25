/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantGradedPieceMap

/-! # Tests for the horizontal graded-piece projection map -/

@[expose] public section

open CategoryTheory Limits CategoryTheory.Pretriangulated

noncomputable section

universe v u

namespace HomologicalComplex₂.FirstQuadrantGradedPieceMapTests

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

example (p : ℕ) : CochainComplex C ℤ :=
  horizontalDirectColumnCochain K p

example (p q : ℕ) :
    (horizontalDirectColumnCochain K p).X (-(p : ℤ) - q) ≅
      (K.X p).X q :=
  horizontalDirectColumnCochainXIso K p q

example (p : ℕ) :
    (horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageUpperIndex p) ⟶
      horizontalDirectColumnCochain K p :=
  horizontalDirectColumnProjectionMap K p

end HomologicalComplex₂.FirstQuadrantGradedPieceMapTests

end
