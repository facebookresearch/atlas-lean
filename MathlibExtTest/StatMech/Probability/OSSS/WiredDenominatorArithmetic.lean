/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.OSSS.WiredDenominatorArithmetic
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.OSSS.WiredDenominatorArithmetic`

* `antitone_sum_Ico_one_le_two_sum_Icc_half` for `a k = 1 / (k + 1)` at `n = 5`.
* `antitone_sum_range_le_two_profile` and `antitone_sum_range_le_two_profile_strict` with
  profile `θ = a`.
-/

@[expose] public section

open StatMech.OSSS

namespace MathlibExtTest.StatMech.Probability.OSSS.WiredDenominatorArithmetic

/-- The antitone sequence `1 / (k + 1)`. -/
noncomputable def a (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)

theorem a_nonneg (k : ℕ) : 0 ≤ a k := by unfold a; positivity

theorem a_anti : Antitone a := fun i j hij => by
  unfold a
  apply one_div_le_one_div_of_le (by positivity)
  have : (i : ℝ) ≤ j := by exact_mod_cast hij
  linarith

example : ∑ k ∈ Finset.Ico 1 5, a k ≤ 2 * ∑ k ∈ Finset.Icc 1 (5 / 2), a k :=
  antitone_sum_Ico_one_le_two_sum_Icc_half a a_nonneg a_anti 5

example : ∑ k ∈ Finset.range 5, a k ≤ 2 * ∑ k ∈ Finset.range 5, a k :=
  antitone_sum_range_le_two_profile a a a_nonneg a_anti a_nonneg 5 le_rfl (fun _ _ => le_rfl)

example : ∑ k ∈ Finset.range 4, a k ≤ 2 * ∑ k ∈ Finset.range 4, a k :=
  antitone_sum_range_le_two_profile_strict a a a_nonneg a_anti a_nonneg 4 le_rfl
    (fun _ _ _ => le_rfl) (fun k _ => a_anti (Nat.zero_le k))

end MathlibExtTest.StatMech.Probability.OSSS.WiredDenominatorArithmetic
