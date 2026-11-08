/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.PartialHadamard

@[expose] public section

namespace MathlibExtTest.PartialHadamard

open MathlibExt.Combinatorics.PartialHadamard

/-- Boundary check: width zero leaves one (empty) matrix. -/
example (n : ℕ) : partialHadamardCount n 0 = 1 :=
  partialHadamardCount_zero_width n

/-- The trivial total-count bound at a concrete size. -/
example : partialHadamardCount 2 4 ≤ 256 := by
  have h := partialHadamardCount_le 2 4
  norm_num at h ⊢
  exact h

/-- The leading term is positive at positive width. -/
example : (0:ℝ) < leadingTerm 2 1 := leadingTerm_pos (by norm_num)

end MathlibExtTest.PartialHadamard
