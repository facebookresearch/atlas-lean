/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.HomologicalAlgebra.CohomologyRank

/-! # Tests for ranks and the block differential

The rank of the identity of a finite-dimensional space is its dimension, the rank of zero is zero,
and the block differential is `(a, b) ↦ (d a, f a - d b)`.
-/

namespace MathlibExtTest.HomologicalAlgebra.CohomologyRank

open _root_.CategoryTheory _root_.MathlibExt.HomologicalAlgebra.CohomologyRank

variable {K : Type} [Field K]

example (V : ModuleCat.{0} K) [FiniteDimensional K V] : homRank (𝟙 V) = Module.finrank K V := by
  rw [homRank, ModuleCat.hom_id, LinearMap.range_id, finrank_top]

example (V W : ModuleCat.{0} K) : homRank (0 : V ⟶ W) = 0 := by
  rw [homRank, ModuleCat.hom_zero, LinearMap.range_zero, finrank_bot]

example {A B : CochainComplex (ModuleCat.{0} K) ℤ} (f : A ⟶ B) (i : ℤ) (a : A.X i)
    (b : B.X (i - 1)) :
    cohomologyBlockDifferential f i (a, b) = (A.d i (i + 1) a, f.f i a - B.d (i - 1) i b) := rfl

end MathlibExtTest.HomologicalAlgebra.CohomologyRank
