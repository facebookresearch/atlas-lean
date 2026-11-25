/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFirstPageSections

/-! # Tests for degreewise first-page column sections -/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂.FirstQuadrantFirstPageSectionsTests

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

example (p q : ℕ) :
    horizontalCompleteDirectColumnSectionComponent K p q ≫
      horizontalDirectColumnProjectionComponent K p q = 𝟙 _ :=
  horizontalCompleteDirectColumnSectionComponent_projection K p q

example (p q : ℕ) :
    horizontalCompleteSuccDirectColumnSection K p q ≫
        (horizontalCompleteDirectColumnProjectionMap K (p + 1)).f
          (-((p + 1 : ℕ) : ℤ) - q) =
      𝟙 _ :=
  horizontalCompleteSuccDirectColumnSection_projection K p q

end HomologicalComplex₂.FirstQuadrantFirstPageSectionsTests

end
