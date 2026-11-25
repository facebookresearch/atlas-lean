/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFiltration

/-! # Tests for the degreewise first-quadrant filtration -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace HomologicalComplex₂.FirstQuadrantFiltrationTests

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

example (k n : ℕ) :
    SplitMono (horizontalFilteredTotalToTotal K k n) :=
  horizontalFilteredTotalToTotalSplitMono K k n

example (k n : ℕ) :
    horizontalFilteredTotalToTotal K k n ≫
        totalToHorizontalFilteredTotal K k n =
      𝟙 (horizontalFilteredTotalObj K k n) :=
  horizontalFilteredTotalToTotal_comp_retraction K k n

end HomologicalComplex₂.FirstQuadrantFiltrationTests

end
