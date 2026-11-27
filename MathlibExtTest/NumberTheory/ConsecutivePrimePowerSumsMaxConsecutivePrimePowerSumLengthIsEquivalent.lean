/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ConsecutivePrimePowerSumsMaxConsecutivePrimePowerSumLengthIsEquivalent

/-!
# Tests for the maximum length of consecutive prime-power sums

The theorem gives ratio limits for sums of prime squares and prime cubes.
-/

namespace MathlibExtTest.NumberTheory.ConsecutivePrimePowerSumsMaxConsecutivePrimePowerSumLengthIsEquivalent

open Asymptotics Filter Finset
open scoped Topology

example : Tendsto (fun x : ℕ =>
    (Nat.findGreatest (fun m => ∑ i ∈ range m, Nat.nth Nat.Prime i ^ 2 ≤ x) x : ℝ) /
      (3 * (x : ℝ) ^ ((1 : ℝ) / 3) / Real.log x ^ ((2 : ℝ) / 3))) atTop (𝓝 1) := by
  have h := MetaMathlibExt.maxConsecutivePrimePowerSumLength_isEquivalent 2 (by decide)
  have hne : ∀ᶠ x : ℕ in atTop,
      (3 * (x : ℝ) ^ ((1 : ℝ) / 3) / Real.log x ^ ((2 : ℝ) / 3)) ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with x hx
    have hx0 : 0 < (x : ℝ) := by positivity
    have hl0 : 0 < Real.log x := Real.log_pos (by exact_mod_cast hx)
    positivity
  apply (isEquivalent_iff_tendsto_one hne).mp
  convert h using 1; norm_num

example : Tendsto (fun x : ℕ =>
    (Nat.findGreatest (fun m => ∑ i ∈ range m, Nat.nth Nat.Prime i ^ 3 ≤ x) x : ℝ) /
      (4 * (x : ℝ) ^ ((1 : ℝ) / 4) / Real.log x ^ ((3 : ℝ) / 4))) atTop (𝓝 1) := by
  have h := MetaMathlibExt.maxConsecutivePrimePowerSumLength_isEquivalent 3 (by decide)
  have hne : ∀ᶠ x : ℕ in atTop,
      (4 * (x : ℝ) ^ ((1 : ℝ) / 4) / Real.log x ^ ((3 : ℝ) / 4)) ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with x hx
    have hx0 : 0 < (x : ℝ) := by positivity
    have hl0 : 0 < Real.log x := Real.log_pos (by exact_mod_cast hx)
    positivity
  apply (isEquivalent_iff_tendsto_one hne).mp
  convert h using 1; norm_num

end MathlibExtTest.NumberTheory.ConsecutivePrimePowerSumsMaxConsecutivePrimePowerSumLengthIsEquivalent
