/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFirstPageMiddleSection

/-! # Tests for middle adjacent-quotient sections -/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂.FirstQuadrantFirstPageMiddleSectionTests

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

example (p q : ℕ) :
    horizontalFirstPageAdjacentMiddleSection K p q ≫
        (horizontalFirstPageAdjacentDirectShortComplex K p).g.f
          (-((p + 1 : ℕ) : ℤ) - q) =
      𝟙 _ :=
  horizontalFirstPageAdjacentMiddleSection_g K p q

end HomologicalComplex₂.FirstQuadrantFirstPageMiddleSectionTests

end
