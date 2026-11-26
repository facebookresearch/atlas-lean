/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.KKL.PBiasedKKLTwoBit

/-!
# Tests for the exact two-bit KKL checks (plus the one-bit dictator check)

Tests for `CSLibExt.Complexity.BooleanFunctions.KKL.PBiasedKKLTwoBit`:

* `pbkt_AND` on the four configurations of `{0, 1}^2`, by `decide`;
* the exact values of `pbkt_AND_expect`, `pbkt_AND_var`, `pbkt_AND_maxInfl`, `pbkt_OR_var` and
  `pbkt_OR_totalInfl` at `p = 1/2` and `p = 3/4`;
* `pbkt_twoBit_atom_numeric` at `x = 1/2`: `2 · 3/16 · log 2 ≤ 1`;
* the headlines `pbkt_OR_kkl_two` at `p = 1/2` and `pbkt_AND_kkl_two` at `p = 3/4`, with the
  exact values substituted, and `pbkt_dictator_kkl_one` (one-bit dictator) at `p = 1/3`.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions

open StatMech StatMech.OSSS StatMech.Probability

example : pbkt_AND (fun _ => true) = true := by decide
example : pbkt_AND (fun i => i = 0) = false := by decide
example : pbkt_AND (fun i => i = 1) = false := by decide
example : pbkt_AND (fun _ => false) = false := by decide

example : expect (bernoulliWeight (1 / 2)) pbkt_andF = 1 / 4 := by
  rw [pbkt_AND_expect]; norm_num

example : var (bernoulliWeight (3 / 4)) pbkt_andF = 63 / 256 := by
  rw [pbkt_AND_var]; norm_num

example : maxInfl (bernoulliWeight (3 / 4)) pbkt_andF = 3 / 4 := pbkt_AND_maxInfl _

example : var (bernoulliWeight (1 / 2)) ctp_f = 3 / 16 := by
  rw [pbkt_OR_var]; norm_num

example : totalInfl (bernoulliWeight (1 / 2)) ctp_f = 1 := by
  rw [pbkt_OR_totalInfl]; norm_num

example : 2 * ((1 - (1 / 2 : ℝ) ^ 2) * (1 / 2) ^ 2) * Real.log (1 / (1 / 2)) ≤ 2 * (1 / 2) :=
  pbkt_twoBit_atom_numeric (by norm_num) (by norm_num)

/-- `pbkt_OR_kkl_two` at `p = 1/2`: `2 · 3/16 · log 2 ≤ 1`. -/
example : 2 * (3 / 16 : ℝ) * Real.log 2 ≤ 1 := by
  have h := pbkt_OR_kkl_two (p := 1 / 2) (by norm_num) (by norm_num)
  rw [pbkt_OR_var, pbkt_OR_maxInfl, pbkt_OR_totalInfl] at h
  norm_num at h ⊢
  linarith

/-- `pbkt_AND_kkl_two` at `p = 3/4`: `2 · 63/256 · log(4/3) ≤ 3/2`. -/
example : 2 * (63 / 256 : ℝ) * Real.log (4 / 3) ≤ 3 / 2 := by
  have h := pbkt_AND_kkl_two (p := 3 / 4) (by norm_num) (by norm_num)
  rw [pbkt_AND_var, pbkt_AND_maxInfl, pbkt_AND_totalInfl] at h
  norm_num at h ⊢
  linarith

example : 2 * var (bernoulliWeight (1 / 3))
      (fun ω : ConfigSpace (Fin 1) => if ω 0 then (1 : ℝ) else 0)
    * Real.log (1 / maxInfl (bernoulliWeight (1 / 3))
      (fun ω : ConfigSpace (Fin 1) => if ω 0 then (1 : ℝ) else 0))
    ≤ totalInfl (bernoulliWeight (1 / 3))
      (fun ω : ConfigSpace (Fin 1) => if ω 0 then (1 : ℝ) else 0) :=
  pbkt_dictator_kkl_one (by norm_num) (by norm_num)

end StatMechTest.BooleanFunctions
