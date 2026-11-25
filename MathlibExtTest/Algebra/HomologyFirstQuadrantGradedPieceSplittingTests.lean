/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantGradedPieceSplitting

/-! # Tests for consecutive-stage splitting data -/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂.FirstQuadrantGradedPieceSplittingTests

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

example (p q : ℕ) : ShortComplex C :=
  horizontalFilteredSuccShortComplex K p q

example (p n : ℕ) :
    horizontalFilteredTotalMap K (Nat.le_succ p) n ≫
      horizontalFilteredSuccRetraction K p n = 𝟙 _ :=
  horizontalFilteredTotalMap_succ_retraction K p n

example (p q : ℕ) :
    horizontalFilteredTopSection K p q ≫
      horizontalFilteredTopProjection K (p + 1) q = 𝟙 _ :=
  horizontalFilteredTopSection_projection K p q

example (p q : ℕ) :
    (horizontalFilteredSuccShortComplex K p q).Splitting :=
  horizontalFilteredSuccSplitting K p q

example (p q : ℕ) :
    (horizontalFilteredSuccShortComplex K p q).Exact :=
  horizontalFilteredSuccShortComplex_exact K p q

end HomologicalComplex₂.FirstQuadrantGradedPieceSplittingTests

end
