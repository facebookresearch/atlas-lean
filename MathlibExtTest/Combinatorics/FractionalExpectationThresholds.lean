/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Combinatorics.FractionalExpectationThresholds

open Set unitInterval
open MathlibExt.Combinatorics.FractionalExpectationThresholdsWanted.FractionalExpectationThresholds

namespace MathlibExtTest.Combinatorics.FractionalExpectationThresholds

-- At the smallest allowed rank the conversion of logarithms is an equality.
example : K * Real.log 2 = 6 * Real.logb 2 4 := by
  have h : Real.log 4 = Real.log 2 + Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  rw [K, Real.logb, h]
  field_simp [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  ring

-- Require both points of a two-point ground set. The only minimal member has size two.
private abbrev both : Set (Set Bool) := {univ}

private theorem rank_both : l both = 2 := by
  classical
  let A : both := ⟨univ, rfl⟩
  have hm : IsMin A := fun B _ => by
    change (univ : Set Bool) ⊆ B.val
    rw [show B.val = univ from B.property]
  have hcard : A.val.ncard = 2 := by simp [A]
  apply le_antisymm
  · exact ciSup_le' fun B => ciSup_le' fun _ => by
      rw [show B.val = univ from B.property]; exact hcard.le
  · rw [← hcard]
    exact le_ciSup_of_le (Set.finite_range _).bddAbove A <|
      le_ciSup_of_le (Set.finite_range _).bddAbove hm le_rfl

-- The one-set cover costs (1/2)^2. It gives a concrete fractional bound, with no use of
-- an assumed threshold theorem: even the trivial upper bound p_c ≤ 1 suffices here.
example : (p_c both : ℝ) ≤ K * q_f both * Real.log (l both) := by
  classical
  let p : I := ⟨1 / 2, by norm_num, by norm_num⟩
  have hc : p ≤ q_c both := by
    apply le_sSup
    refine ⟨⟨?_, ?_⟩, {univ}, ?_, ?_⟩
    · change (0 : ℝ) < 1 / 2; norm_num
    · change (1 / 2 : ℝ) < 1; norm_num
    · rintro T (rfl : T = univ)
      exact ⟨univ, by simp, Subset.rfl⟩
    · norm_num [p, Set.ncard_univ, Nat.card_eq_fintype_card]
  have hf : (1 / 2 : ℝ) ≤ q_f both := hc.trans (q_c_le_q_f both)
  rw [rank_both, Nat.cast_ofNat, K]
  calc
    _ ≤ 1 := (p_c both).2.2
    _ ≤ 12 * (q_f both : ℝ) := by linarith
    _ = _ := by field_simp [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

end MathlibExtTest.Combinatorics.FractionalExpectationThresholds
