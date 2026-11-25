/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFilteredComplex

/-! # Tests for first-quadrant filtered total complexes -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace HomologicalComplex₂.FirstQuadrantFilteredComplexTests

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

example (k : ℕ) : ChainComplex C ℕ :=
  horizontalFilteredTotalComplex K k

example (k m : ℕ) :
    (horizontalFilteredTotalComplex K k).d (m + 1) m ≫
        horizontalFilteredTotalToTotal K k m =
      horizontalFilteredTotalToTotal K k (m + 1) ≫
        (K.total (ComplexShape.down ℕ)).d (m + 1) m :=
  horizontalFilteredTotalD_toTotal K k m

end HomologicalComplex₂.FirstQuadrantFilteredComplexTests

end
