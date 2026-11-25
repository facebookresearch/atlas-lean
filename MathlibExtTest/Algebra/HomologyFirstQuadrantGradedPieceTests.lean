/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantGradedPiece

/-! # Tests for horizontal graded-piece ingredients -/

@[expose] public section

open CategoryTheory Limits CategoryTheory.Pretriangulated

noncomputable section

universe v u

namespace HomologicalComplex₂.FirstQuadrantGradedPieceTests

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

example (p : ℕ) : CochainComplex C ℤ :=
  horizontalColumnCochain K p

example (p q : ℕ) :
    (horizontalColumnCochain K p).X (-(p : ℤ) - q) ≅
      (K.X p).X q :=
  horizontalColumnCochainXIso K p q

example (p : ℕ) :
    horizontalCompleteFilteredTotalMonoOver K
        (horizontalFirstPageUpperIndex p) ≅
      (horizontalTotalFiltration K).toMonoOver.obj p :=
  horizontalCompleteFilteredTotalMonoOverUpperIso K p

example (p : ℕ) :
    (horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageUpperIndex p) ≅
      (ComplexShape.embeddingDownNat.extendFunctor C).obj
        ((horizontalTotalFiltration K).toMonoOver.obj p).obj.left :=
  horizontalCompleteFiltrationCochainMonoUpperIso K p

example (p q : ℕ) :
    ((horizontalCompleteFiltrationCochainDiagram K).obj
      (horizontalFirstPageUpperIndex p)).X (-(p : ℤ) - q) ⟶
        (horizontalColumnCochain K p).X (-(p : ℤ) - q) :=
  horizontalColumnProjectionComponent K p q

example (p : ℕ) (i : ℤ) :
    ((horizontalCompleteFiltrationCochainDiagram K).obj
      (horizontalFirstPageUpperIndex p)).X i ⟶
        (horizontalColumnCochain K p).X i :=
  horizontalColumnProjection K p i

example (p q : ℕ) :
    horizontalFilteredTotalMap K (Nat.le_succ p) (p + 1 + q) ≫
      horizontalFilteredTopProjection K (p + 1) q = 0 :=
  horizontalFilteredTotalMap_succ_topProjection K p q

example (p q : ℕ) :
    horizontalFilteredTotalD K p (p + q + 1) (p + q) ≫
        horizontalFilteredTopProjection K p q =
      horizontalFilteredTopProjection K p (q + 1) ≫
        (ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ) (p, q + 1) • (K.X p).d (q + 1) q) :=
  horizontalFilteredTotalD_topProjection K p q

end HomologicalComplex₂.FirstQuadrantGradedPieceTests

end
