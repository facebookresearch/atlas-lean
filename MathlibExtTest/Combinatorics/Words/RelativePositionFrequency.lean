/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Words.RelativePositionFrequency
import Mathlib.Algebra.Order.Floor.Semifield

/-! # Test of the relative position limit for a periodic word -/

namespace MetaMathlibExt.tendsto_relativePosition_div_of_frequency

open Filter Topology

-- In abbabb…, two letters out of every three are b, so the signed limit is negative.
private def abb (i : ℕ) : Bool := decide (i % 3 = 0)

example : Tendsto (fun n : ℕ => (relativePosition abb n : ℝ) / n) atTop (𝓝 (-3 / 2)) := by
  have count (m : ℕ) : letterCount abb false m = 2 * m / 3 := by
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [letterCount_succ, ih]
      simp only [abb, decide_eq_false_iff_not]
      have residues : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
      rcases residues with h | h | h <;> simp [h] <;> omega
  have freq : Tendsto (fun m : ℕ => (letterCount abb false m : ℝ) / m) atTop (𝓝 (2 / 3)) := by
    apply ((tendsto_nat_floor_mul_div_atTop (by norm_num : (0 : ℝ) ≤ 2 / 3)).comp
      tendsto_natCast_atTop_atTop).congr
    intro m
    simp only [Function.comp_apply, count, div_mul_eq_mul_div, ← Nat.floor_div_eq_div (K := ℝ)]
    norm_cast
  convert tendsto_relativePosition_div_of_frequency (by norm_num) (by norm_num) freq using 2
  norm_num

end MetaMathlibExt.tendsto_relativePosition_div_of_frequency
