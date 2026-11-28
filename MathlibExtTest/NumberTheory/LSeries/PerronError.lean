/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LSeries.PerronError

/-!
# Tests for the Perron error estimates

Values of `PerronKernel.perronStep` on both sides of and at the jump, and instantiations of the
kernel estimate and the elementary sums.
-/

@[expose] public section

open PerronKernel

namespace PerronErrorTest

example : perronStep 0 = 0 := perronStep_of_lt_one (by norm_num)

example : perronStep (-3) = 0 := perronStep_of_lt_one (by norm_num)

example : perronStep 1 = 1 / 2 := perronStep_one

example : perronStep 2 = 1 := perronStep_of_one_lt (by norm_num)

example : perronStep (1 / 2) = 0 := by norm_num [perronStep]

/-- The kernel estimate at `x = 2`, `c = 1`, `T = 1`. -/
example : ‖((1 / (2 * Real.pi)) • ∫ t in (-1 : ℝ)..1,
      ((2 : ℝ) : ℂ) ^ (((1 : ℝ) : ℂ) + (t : ℂ) * Complex.I) /
        (((1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) - ((perronStep 2 : ℝ) : ℂ)‖ <
    (2 : ℝ) ^ (1 : ℝ) * min 1 (1 / (1 * |Real.log 2|)) :=
  norm_truncated_sub_perronStep_lt (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `∑_{n < N} (n + 1)^{-2} ≤ 2`. -/
example (N : ℕ) : ∑ n ∈ Finset.range N, ((n : ℝ) + 1) ^ (-(2 : ℝ)) ≤ 2 := by
  have := sum_range_add_one_rpow_neg_le (s := 2) (by norm_num) N
  norm_num at this ⊢
  linarith

end PerronErrorTest
