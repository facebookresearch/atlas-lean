/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Hypercontractivity.SmallSetExpansion

open BooleanCube
open scoped BigOperators

/-! ### Small-set expansion -/

/-- (p,2)-hypercontractivity at `ρ = 1/2`: `Stab_{1/2}[f] ≤ ‖f‖_{3/2}²`. -/
example (f : BoolCube 4 → ℝ) :
    boolNoiseStab (1 / 2) f ≤ StatMech.Probability.bnt_qnorm (1 + 1 / 2) f ^ 2 :=
  boolNoiseStab_le_bnt_qnorm_sq (by norm_num) (by norm_num) f

/-- Small-set expansion for the indicator of the half-cube `{x | x 0 = true}`. -/
example : boolNoiseStab (1 / 3) (fun x : BoolCube 3 => if x 0 then (1 : ℝ) else 0) ≤
    (𝔼 x : BoolCube 3, if x 0 then (1 : ℝ) else 0) ^ (2 / (1 + 1 / 3 : ℝ)) :=
  boolNoiseStab_le_rpow_of_indicator (by norm_num) (by norm_num)
    (fun x => by by_cases h : x 0 <;> simp [h])

/-- At `ρ = 0` the bound is `α²`, attained: `Stab_0[1_A] = α²`. -/
example (f : BoolCube 3 → ℝ) (hf : ∀ x, f x = 0 ∨ f x = 1) :
    boolNoiseStab 0 f ≤ (𝔼 x, f x) ^ (2 / (1 + 0 : ℝ)) :=
  boolNoiseStab_le_rpow_of_indicator le_rfl zero_le_one hf
