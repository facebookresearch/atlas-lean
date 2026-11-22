/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.SpecificLimits.Normed
import MathlibExt.Analysis.Series.DirichletTest

set_option autoImplicit false

open Finset Filter Topology

-- `∑ (-1)^n (1/2)^n` converges, with `v n = (1/2)^n`; the partial sums of `(-1)^k` are
-- `(1 + (-1)^n) / 2`, so they are bounded by `1`.
example : ∃ l, Tendsto (fun N => ∑ i ∈ range N, ((-1 : ℂ)) ^ i * (1 / 2) ^ i) atTop (𝓝 l) := by
  refine Complex.exists_tendsto_sum_range_mul_of_bounded_of_summable_norm_sub _ _ ?_ ?_ ?_
  · have h : ∀ n, ∑ k ∈ range (n + 1), ((-1 : ℂ)) ^ k = (1 + (-1) ^ n) / 2 := by
      intro n
      induction n with
      | zero => norm_num
      | succ n ih => rw [sum_range_succ, ih, pow_succ]; ring
    refine ⟨1, fun n => ?_⟩
    rw [h, norm_div, show ‖(2 : ℂ)‖ = 2 by simp]
    have := norm_add_le (1 : ℂ) ((-1) ^ n)
    rw [norm_one, norm_pow, norm_neg, norm_one, one_pow] at this
    linarith
  · exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num)
  · refine (summable_geometric_two.mul_right (1 / 2)).congr fun n => ?_
    rw [pow_succ, ← mul_one_sub, norm_mul, norm_pow]
    norm_num
