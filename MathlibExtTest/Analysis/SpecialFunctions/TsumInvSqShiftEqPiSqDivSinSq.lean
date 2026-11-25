/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.SpecialFunctions.TsumInvSqShiftEqPiSqDivSinSq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open MathlibExt.Analysis.SpecialFunctions.TsumInvSqShiftEqPiSqDivSinSqWanted

namespace MathlibExtTest.Analysis.SpecialFunctions.TsumInvSqShiftEqPiSqDivSinSq

private theorem half_add_int_not_integer (k : ℤ) :
    (k : ℝ) + 1 / 2 ∉ Set.range (fun n : ℤ => (n : ℝ)) := by
  rintro ⟨n, hn⟩
  have h : 2 * n = 2 * k + 1 := by
    exact_mod_cast (show 2 * (n : ℝ) = 2 * (k : ℝ) + 1 by linarith)
  omega

example : (∑' n : ℤ, 1 / (((1 / 2 : ℝ) + n) ^ 2)) = Real.pi ^ 2 := by
  have hu : (1 / 2 : ℝ) ∉ Set.range (fun n : ℤ => (n : ℝ)) := by
    simpa using half_add_int_not_integer 0
  rw [tsum_one_div_add_int_sq_eq_pi_sq_div_sin_sq (hu := hu)]
  rw [show Real.pi * (1 / 2) = Real.pi / 2 by ring, Real.sin_pi_div_two]
  simp

example : (∑' n : ℤ, 1 / (((-(3 / 2) : ℝ) + n) ^ 2)) = Real.pi ^ 2 := by
  have hu : (-(3 / 2) : ℝ) ∉ Set.range (fun n : ℤ => (n : ℝ)) := by
    have h := half_add_int_not_integer (-2)
    norm_num at h ⊢
    exact h
  rw [tsum_one_div_add_int_sq_eq_pi_sq_div_sin_sq (hu := hu)]
  rw [show Real.pi * (-(3 / 2)) = -(Real.pi / 2 + Real.pi) by ring,
    Real.sin_neg, Real.sin_add_pi, Real.sin_pi_div_two]
  norm_num

end MathlibExtTest.Analysis.SpecialFunctions.TsumInvSqShiftEqPiSqDivSinSq
