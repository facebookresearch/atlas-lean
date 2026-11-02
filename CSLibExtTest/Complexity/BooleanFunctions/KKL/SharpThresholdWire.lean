/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.KKL.SharpThresholdWire
public import CSLibExt.Complexity.BooleanFunctions.Hypercontractivity.DecoupledTwoPointRefutation
public import CSLibExtTest.Complexity.BooleanFunctions.KKL.KKLEvents

/-!
# Tests for the sharp-threshold wiring

Tests for `CSLibExt.Complexity.BooleanFunctions.KKL.SharpThresholdWire`:

* the exponent and coefficient computations `stw_master_q_value`, `stw_ranges_meet_only_at_two`,
  `stw_variance_coeff_gap` (at `p = 1/4`), `stw_coeff_gap_eq_iff_half` (true at `1/2`, false at
  `3/4`) and `stw_verdict` at `u = 1/2`, `p = 3/4`;
* `stw_kkl_logGain_half` at the `AND` function on `{0, 1}^Bool`: `2 · 3/16 · log 2 ≤ 1`;
* the remaining goal `stw_RemainingGoal q` (definitionally `∀ p ∈ (1/2, q), PBiasedHCLib p`)
  holds for `q ≤ 1/2` (`stw_RemainingGoal_empty_window`) and fails for every `q > 9/10`
  (`dtpc_remainingGoal_false`); for `q ∈ (1/2, 9/10]` it is neither proved nor refuted here.
  `stw_rhoOptimise_of_lib` and `stw_sharpThreshold_of_lib` are instantiated at the degenerate
  `q = 1/2` (the latter for the dictator event). `PBiasedHCLib` itself is non-trivial: true at
  `1/2` (`htl_lib_half`), false at `9/10` (`dtpc_pbiasedHCLib_nine_tenths_false`).
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions

open StatMech StatMech.OSSS StatMech.Probability

example : (1 + (Real.sqrt (1 - 1 / 2)) ^ 2 : ℝ) = 2 - 1 / 2 :=
  stw_master_q_value _ (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 - 1 / 2))

example {q : ℝ} (h1 : 2 ≤ q ∧ q ≤ 4) (h2 : 1 < q ∧ q ≤ 2) : q = 2 :=
  stw_ranges_meet_only_at_two h1 h2

example : 4 * (1 / 4 : ℝ) ^ 2 * (1 - 1 / 4) ^ 2 ≤ 1 / 4 * (1 - 1 / 4) :=
  stw_variance_coeff_gap (by norm_num) (by norm_num)

example : 4 * (1 / 2 : ℝ) ^ 2 * (1 - 1 / 2) ^ 2 = 1 / 2 * (1 - 1 / 2) :=
  (stw_coeff_gap_eq_iff_half (by norm_num) (by norm_num)).mpr rfl

example : 4 * (3 / 4 : ℝ) ^ 2 * (1 - 3 / 4) ^ 2 ≠ 3 / 4 * (1 - 3 / 4) := fun h =>
  absurd ((stw_coeff_gap_eq_iff_half (by norm_num) (by norm_num)).mp h) (by norm_num)

example : (1 < 2 - (1 / 2 : ℝ) ∧ 2 - (1 / 2 : ℝ) ≤ 2) ∧
    4 * (3 / 4 : ℝ) ^ 2 * (1 - 3 / 4) ^ 2 < 3 / 4 * (1 - 3 / 4) :=
  stw_verdict (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `stw_kkl_logGain_half` at `AND`: `2 · 3/16 · log 2 ≤ 1`. -/
example : 2 * (3 / 16 : ℝ) * Real.log 2 ≤ 1 := by
  have h := stw_kkl_logGain_half andFun
  rw [← kkl_var_indicator_eq, var_andFun, maxInfl_andInd, totalInfl_andInd] at h
  norm_num at h ⊢
  linarith

example : PBiasedHCLib (1 / 2) ∧ ¬ PBiasedHCLib (9 / 10) :=
  ⟨htl_lib_half, dtpc_pbiasedHCLib_nine_tenths_false⟩

example : ¬ stw_RemainingGoal 1 := dtpc_remainingGoal_false (by norm_num)

example : ptn_RhoOptimise (1 / 2) := stw_rhoOptimise_of_lib (stw_RemainingGoal_empty_window le_rfl)

example : 1 / 2 + (2 * 1 * 1) * ((1 / 2 : ℝ) - 1 / 2) ≤ StatMech.prob (1 / 2) dictEvent := by
  classical
  exact stw_sharpThreshold_of_lib (by norm_num) (stw_RemainingGoal_empty_window le_rfl) dictEvent
    dictEvent_isIncreasing le_rfl zero_le_one zero_le_one prob_dictEvent (by simp) (by simp)

end StatMechTest.BooleanFunctions
