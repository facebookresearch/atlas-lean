/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFirstPageConnecting

/-! # Tests for first-page connecting maps -/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂.FirstQuadrantFirstPageConnectingTests

section

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

example (p q : ℕ) :
    horizontalFilteredTopSection K p q ≫
        horizontalFilteredTotalD K (p + 1) (p + 1 + q) (p + q) ≫
        horizontalFilteredPreviousColumnProjection K p q =
      (K.d (p + 1) p).f q :=
  horizontalFilteredTopSection_d_previousColumnProjection_eq K p q

end

section

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

example (p q : ℕ) :
    (horizontalDirectColumnCochain K (p + 1)).homology
        (-((p + 1 : ℕ) : ℤ) - q) ⟶
      (horizontalDirectColumnCochain K p).homology (-(p : ℤ) - q) :=
  horizontalFirstPageAdjacentConnectingMap K p q

example (p q : ℕ) :
    (K.X (p + 1)).homology q ⟶ (K.X p).homology q :=
  horizontalFirstPageAdjacentVerticalConnectingMap K p q

example (p q : ℕ) :
    (K.X (p + 1)).homology q ⟶ (K.X p).homology q :=
  horizontalFirstPageHorizontalHomologyMap K p q

end

end HomologicalComplex₂.FirstQuadrantFirstPageConnectingTests

end
