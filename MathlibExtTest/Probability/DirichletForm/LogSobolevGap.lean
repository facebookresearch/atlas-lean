/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.DirichletForm.LogSobolevGap
public import MathlibExtTest.Probability.DirichletForm.SpectralGap

import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Tests for `2α ≤ λ`

For the two-state chain `K₂` with uniform `π₂` (spectral gap `1`), the theorem gives
`α ≤ 1/2`. `K₂ - 1` is half the generator of the flip chain of Diaconis and Saloff-Coste (1996),
Example 3.1, for which they report `α = λ/2 = 1`; halving the form halves both constants, so the
bound is attained here (not formalised). The cubic Taylor bound is checked at `u = 0`
and `u = 1/2`.
-/

set_option autoImplicit false

open MathlibExt.Probability.DirichletForm
open MathlibExtTest.Probability.DirichletForm.SpectralGap

namespace MathlibExtTest.Probability.DirichletForm.LogSobolevGap

example : logSobolevConstant π₂ K₂ ≤ 1 / 2 := by
  have h := two_mul_logSobolevConstant_le_spectralGap (π := π₂) (P := K₂)
    (fun _ => by norm_num [π₂])
    (by simp [π₂]) (fun _ _ => by simp [K₂]) (fun x => by simp [K₂])
  rw [spectralGap_K₂] at h
  linarith

example : |(1 + (1 / 2 : ℝ)) * Real.log (1 + 1 / 2) - (1 / 2 + (1 / 2) ^ 2 / 2)| ≤
    4 * |(1 / 2 : ℝ)| ^ 3 :=
  abs_mul_log_one_add_sub_le (by norm_num [abs_of_pos])

example : |(1 + (0 : ℝ)) * Real.log (1 + 0) - (0 + 0 ^ 2 / 2)| ≤ 4 * |(0 : ℝ)| ^ 3 :=
  abs_mul_log_one_add_sub_le (by norm_num)

end MathlibExtTest.Probability.DirichletForm.LogSobolevGap
