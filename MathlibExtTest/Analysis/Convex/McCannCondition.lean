/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.McCannCondition
import Mathlib.Tactic.NormNum

@[expose] public section

open Real MathlibExt.Analysis.Convex.McCann

namespace MathlibExtTest.Analysis.Convex.McCannCondition

/-- The entropy satisfies McCann's condition in dimension `3`. -/
example : McCannCondition 3 (fun s => s * log s) := mcCannCondition_entropy 3

/-- The dilation profile of the entropy at `λ = e` in dimension `2` is `-2`. -/
example : dilationProfile 2 (fun s => s * log s) (exp 1) = -2 := by
  rw [dilationProfile_entropy 2 (exp_pos 1), log_exp]; norm_num

/-- The porous-medium energy `s² / (2 - 1)` satisfies McCann's condition in every dimension. -/
example (d : ℕ) : McCannCondition d (fun s => s ^ (2 : ℝ) / (2 - 1)) :=
  mcCannCondition_porousMedium_of_one_lt d (by norm_num)

/-- In dimension `2`, the fast-diffusion exponent `m = 1/2` is at McCann's threshold `1 - 1/2`. -/
example : McCannCondition 2 (fun s => s ^ (1 / 2 : ℝ) / (1 / 2 - 1)) :=
  (mcCannCondition_porousMedium_iff (by norm_num) (by norm_num) (by norm_num)).2 (by norm_num)

/-- In dimension `2`, the exponent `m = 1/3` is below the threshold: condition (A1) fails. -/
example : ¬ McCannCondition 2 (fun s => s ^ (1 / 3 : ℝ) / (1 / 3 - 1)) := by
  rw [mcCannCondition_porousMedium_iff (by norm_num) (by norm_num) (by norm_num)]
  norm_num

end MathlibExtTest.Analysis.Convex.McCannCondition
