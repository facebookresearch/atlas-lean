/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Hypercontractivity.FiniteExponentialRateComparison

/-!
# Tests for `MathlibExt.Probability.Hypercontractivity.FiniteExponentialRateComparison`

* `pow_negLogRate_le_negLogRate_of_mul_le_mul_pow` for `tail_n = e^{-2(n+1)}`,
  `corr_n = e^{-(n+1)}`, `height_n = n + 1`, `k = 2`: the rates `1` and `2` satisfy `2 · 1 ≤ 2`.
* The one-step bound at `a = b = 1`.
-/

@[expose] public section

open StatMech.Probability Filter

namespace MathlibExtTest.StatMech.Probability.Hypercontractivity.FiniteExponentialRateComparison

example : (2 : ℕ) * (-Real.log (Real.exp (-1)) / ((1 : ℕ) : ℝ)) ≤
    -Real.log (Real.exp (-2)) / ((1 : ℕ) : ℝ) + (Real.log 1 - Real.log 1) / ((1 : ℕ) : ℝ) :=
  pow_negLog_div_le_negLog_div_add_const_of_mul_le_mul_pow one_pos one_pos (Real.exp_pos _)
    (Real.exp_pos _) one_pos (by rw [one_mul, one_mul, ← Real.exp_nat_mul]; norm_num)

example : ((2 : ℕ) : ℝ) * 1 ≤ 2 :=
  pow_negLogRate_le_negLogRate_of_mul_le_mul_pow (tail := fun n => Real.exp (-(2 * (n + 1))))
    (corr := fun n => Real.exp (-(n + 1))) (height := fun n => n + 1) (a := 1) (b := 1)
    one_pos one_pos (fun _ => Real.exp_pos _) (fun _ => Real.exp_pos _) (fun _ => Nat.succ_pos _)
    (tendsto_add_atTop_nat 1)
    (fun n => by rw [one_mul, one_mul, ← Real.exp_nat_mul]; push_cast; ring_nf; rfl)
    (by
      refine tendsto_const_nhds.congr fun n => ?_
      rw [Real.log_exp]; push_cast; field_simp)
    (by
      refine tendsto_const_nhds.congr fun n => ?_
      rw [Real.log_exp]; push_cast; field_simp)

end MathlibExtTest.StatMech.Probability.Hypercontractivity.FiniteExponentialRateComparison
