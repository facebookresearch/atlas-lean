/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.Gamma.MulLogUpperBound

open MetaMathlibExt Real

-- At the first admissible integer, the Gamma values reduce to factorials.
example : 120 * log 120 ≤ (24 : ℝ) ^ (24 : ℕ) := by
  convert Gamma_add_one_mul_log_le_Gamma_rpow_self (x := 5) (by norm_num) using 1 <;>
    norm_num [Nat.factorial]

-- Between 4 and 5, positivity lets us isolate the logarithm.
example : log (Gamma (11 / 2)) ≤ Gamma (9 / 2) ^ Gamma (9 / 2) / Gamma (11 / 2) := by
  apply (le_div_iff₀ (Gamma_pos_of_pos (by norm_num))).2
  rw [mul_comm]
  convert Gamma_add_one_mul_log_le_Gamma_rpow_self (x := 9 / 2) (by norm_num) using 1
  norm_num
