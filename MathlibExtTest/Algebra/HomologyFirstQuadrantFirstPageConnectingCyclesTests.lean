/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFirstPageConnectingCycles

/-! # Tests for the adjacent connecting map on cycles -/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂.FirstQuadrantFirstPageConnectingCyclesTests

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

example (p q : ℕ) :
    (horizontalDirectColumnCochain K (p + 1)).homologyπ
        (-((p + 1 : ℕ) : ℤ) - q) ≫
      horizontalFirstPageAdjacentConnectingMap K p q =
    (horizontalDirectColumnCochain K p).liftCycles
        (horizontalFirstPageAdjacentBoundaryCycles K p q)
        (-(p : ℤ) - q + 1) (by simp)
        (horizontalFirstPageAdjacentBoundaryCycles_d K p q) ≫
      (horizontalDirectColumnCochain K p).homologyπ (-(p : ℤ) - q) :=
  horizontalFirstPageAdjacentConnectingMap_eq_boundaryCycles K p q

end HomologicalComplex₂.FirstQuadrantFirstPageConnectingCyclesTests

end
