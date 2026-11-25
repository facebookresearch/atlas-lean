/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.KJacobsthal
import Mathlib.Tactic.NormNum.RealSqrt

/-! # Tests for the k-Jacobsthal sequences -/

namespace MetaMathlibExt.tendsto_lucasU_kJacobsthal_ratio.Tests

-- The smallest admissible parameter gives the classical Jacobsthal ratio limit.
example : Filter.Tendsto
    (fun n : ℕ => (lucasU (kJacobsthalParams 1) (n + 1) : ℝ) / lucasU (kJacobsthalParams 1) n)
    Filter.atTop (nhds 2) := by
  have h := tendsto_lucasU_kJacobsthal_ratio 1 (by decide)
  norm_num at h
  exact h

-- At the excluded parameter, every even-indexed denominator vanishes.
example (n : ℕ) : lucasU (kJacobsthalParams 0) (2 * n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.mul_succ, lucasU_add_two, ih]
    simp [kJacobsthalParams]

-- The companion recurrence also accepts negative initial values.
example : companionKJacobsthal 2 (-3) 1 3 = -6 := by decide

end MetaMathlibExt.tendsto_lucasU_kJacobsthal_ratio.Tests
