/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.HomologicalAlgebra.CohomologyRank
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Finite

/-! # Tests for ranks and the block differential

The rank of the identity is the dimension of the space (and is nonzero on the infinite-dimensional
space `ℚ[X]`), the rank of zero is zero, and the block differential is `(a, b) ↦ (d a, f a - d b)`.
-/

namespace MathlibExtTest.HomologicalAlgebra.CohomologyRank

open _root_.CategoryTheory _root_.MathlibExt.HomologicalAlgebra.CohomologyRank

variable {K : Type} [Field K]

/-- The identity has the rank of the space, finite or not. -/
example (V : ModuleCat.{0} K) : homRank (𝟙 V) = Module.rank K V := by
  rw [homRank, ModuleCat.hom_id, LinearMap.range_id, rank_top]

example (V : ModuleCat.{0} K) [FiniteDimensional K V] : homRank (𝟙 V) = Module.finrank K V := by
  rw [homRank, ModuleCat.hom_id, LinearMap.range_id, rank_top, Module.finrank_eq_rank]

example (V W : ModuleCat.{0} K) : homRank (0 : V ⟶ W) = 0 := by
  rw [homRank, ModuleCat.hom_zero, LinearMap.range_zero, rank_bot]

/-- On an infinite-dimensional space the identity does not have rank zero. -/
example : homRank (𝟙 (ModuleCat.of ℚ (Polynomial ℚ))) ≠ 0 := by
  rw [homRank, ModuleCat.hom_id, LinearMap.range_id, rank_top]
  exact (rank_pos (R := ℚ) (M := Polynomial ℚ)).ne'

example {A B : CochainComplex (ModuleCat.{0} K) ℤ} (f : A ⟶ B) (i : ℤ) (a : A.X i)
    (b : B.X (i - 1)) :
    cohomologyBlockDifferential f i (a, b) = (A.d i (i + 1) a, f.f i a - B.d (i - 1) i b) := rfl

end MathlibExtTest.HomologicalAlgebra.CohomologyRank
