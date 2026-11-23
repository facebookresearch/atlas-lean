/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.Gamma.BetaIntegralDecay

set_option autoImplicit false

-- The sharp bound, at `m = 3`, `β = 1`.
example : ∫ r in (0 : ℝ)..1, r ^ 3 * (1 - r) ^ (1 : ℝ) ≤ (3 : ℝ) ^ (-((1 : ℝ) + 1)) * Real.Gamma (1 + 1) :=
  intervalIntegral_pow_mul_one_sub_rpow_le 3 (by norm_num) zero_le_one

-- `Γ(β + 1) ≤ 2` at both ends of `[0, 2]`, where it is an equality at `β = 2`.
example : Real.Gamma (0 + 1) ≤ 2 := Real.Gamma_add_one_le_two le_rfl (by norm_num)
example : Real.Gamma (2 + 1) ≤ 2 := Real.Gamma_add_one_le_two (by norm_num) le_rfl

-- The textbook's constant, at the largest allowed `β`.
example (m : ℕ) (hm : 1 ≤ m) :
    ∫ r in (0 : ℝ)..1, r ^ m * (1 - r) ^ (2 : ℝ) ≤ 100 * (m : ℝ) ^ (-(1 + (2 : ℝ))) :=
  intervalIntegral_pow_mul_one_sub_rpow_le_hundred m hm (by norm_num) le_rfl
