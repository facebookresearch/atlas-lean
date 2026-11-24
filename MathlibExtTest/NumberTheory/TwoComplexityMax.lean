/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TwoComplexityMax

/-! # Tests for the largest number built from a fixed number of copies -/

namespace MathlibExt.NumberTheory.TwoComplexityWanted

-- With one copy, the maximum is the base itself.
example (l : ℕ) (hl : 1 < l) : IsGreatest {n | CanBuild l 1 n} l := by
  simpa only [IsGreatest, upperBounds, Set.mem_ofPred_eq, pow_one] using
    canBuild_max l 1 hl le_rfl

-- At the smallest base, addition can also attain the two-copy maximum.
example : IsGreatest {n | CanBuild 2 2 n} (2 + 2) :=
  ⟨CanBuild.base.add CanBuild.base, fun _ h => (canBuild_max 2 2 (by decide) (by decide)).2 _ h⟩

-- Three copies of three cannot reach the successor of their maximum.
example : ¬ CanBuild 3 3 28 := fun h =>
  (by decide : ¬ 28 ≤ 3 ^ 3) ((canBuild_max 3 3 (by decide) (by decide)).2 _ h)

end MathlibExt.NumberTheory.TwoComplexityWanted
