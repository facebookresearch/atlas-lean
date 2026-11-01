/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Hypercontractivity.BonamiTwoPoint

/-!
# Tests for `MathlibExt.Probability.Hypercontractivity.BonamiTwoPoint`

* `bts_twoPointScalar` (the two-point Bonami inequality) applied at `ρ = 1/2` for arbitrary
  `a, b`, and evaluated at `ρ = 1` (`q = 2`, where it is the parallelogram identity) and at
  `ρ = 0`, `a = b = 1` (both sides equal `1`);
* `bts_taylor_lower` applied at `q = 3/2`, `t = 1/2`.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Probability.Hypercontractivity.BonamiTwoPoint

open _root_.StatMech.Probability

-- `bts_twoPointScalar` at `ρ = 1/2`, with the hypotheses `0 ≤ ρ ≤ 1` discharged.
example (a b : ℝ) : a ^ 2 + (1 / 2 : ℝ) ^ 2 * b ^ 2
    ≤ ((|a + b| ^ (1 + (1 / 2 : ℝ) ^ 2) + |a - b| ^ (1 + (1 / 2 : ℝ) ^ 2)) / 2)
      ^ (2 / (1 + (1 / 2 : ℝ) ^ 2)) :=
  bts_twoPointScalar (by norm_num) (by norm_num) a b

-- At `ρ = 1` the exponent is `q = 2` and the conclusion is `a² + b² ≤ ((a+b)² + (a-b)²)/2`.
example (a b : ℝ) : a ^ 2 + b ^ 2 ≤ ((a + b) ^ 2 + (a - b) ^ 2) / 2 := by
  have h := bts_twoPointScalar (ρ := 1) (by norm_num) le_rfl a b
  have h2 : (1 : ℝ) + 1 ^ 2 = 2 := by norm_num
  rw [h2, show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one, Real.rpow_two, Real.rpow_two,
    sq_abs, sq_abs, one_pow, one_mul] at h
  exact h

-- At `ρ = 0`, `a = b = 1` both sides equal `1`.
example : (1 : ℝ) ^ 2 + 0 ^ 2 * 1 ^ 2
    ≤ ((|(1 : ℝ) + 1| ^ (1 + (0 : ℝ) ^ 2) + |(1 : ℝ) - 1| ^ (1 + (0 : ℝ) ^ 2)) / 2)
      ^ (2 / (1 + (0 : ℝ) ^ 2)) ∧
    ((|(1 : ℝ) + 1| ^ (1 + (0 : ℝ) ^ 2) + |(1 : ℝ) - 1| ^ (1 + (0 : ℝ) ^ 2)) / 2)
      ^ (2 / (1 + (0 : ℝ) ^ 2)) = 1 := by
  refine ⟨bts_twoPointScalar le_rfl zero_le_one 1 1, ?_⟩
  norm_num

-- `bts_taylor_lower` at `q = 3/2`, `t = 1/2`.
example : 2 + (3 / 2 : ℝ) * (3 / 2 - 1) * (1 / 2) ^ 2
    ≤ (1 + 1 / 2 : ℝ) ^ (3 / 2 : ℝ) + (1 - 1 / 2 : ℝ) ^ (3 / 2 : ℝ) :=
  bts_taylor_lower (by norm_num) (by norm_num) (by norm_num [abs_of_pos])

end MathlibExtTest.StatMech.Probability.Hypercontractivity.BonamiTwoPoint
