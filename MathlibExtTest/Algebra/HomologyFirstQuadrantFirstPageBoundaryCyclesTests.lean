/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFirstPageBoundaryCycles

/-! # Tests for adjacent-column boundary cycles -/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂.FirstQuadrantFirstPageBoundaryCyclesTests

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

example (p q : ℕ) :
    horizontalFirstPageAdjacentBoundaryCycles K p q ≫
        (horizontalFirstPageAdjacentDirectShortComplex K p).f.f
          (-(p : ℤ) - q) =
      (horizontalDirectColumnCochain K (p + 1)).iCycles
          (-((p + 1 : ℕ) : ℤ) - q) ≫
        horizontalFirstPageAdjacentMiddleSection K p q ≫
        (horizontalFirstPageAdjacentDirectShortComplex K p).X₂.d
          (-((p + 1 : ℕ) : ℤ) - q) (-(p : ℤ) - q) :=
  horizontalFirstPageAdjacentBoundaryCycles_f K p q

example (p q : ℕ) :
    horizontalFirstPageAdjacentBoundaryCycles K p q ≫
      (horizontalDirectColumnCochain K p).d
        (-(p : ℤ) - q) (-(p : ℤ) - q + 1) = 0 :=
  horizontalFirstPageAdjacentBoundaryCycles_d K p q

end HomologicalComplex₂.FirstQuadrantFirstPageBoundaryCyclesTests

end
