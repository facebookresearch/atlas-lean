/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimeCounting.AlmostPrimeUniformUpperBound
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt

-- At the endpoint `t = 1`, the bound forces the count to vanish for every `k ≥ 1`.
example (k : ℕ) (hk : 1 ≤ k) : almostPrimeCounting (k + 1) 1 = 0 := by
  obtain ⟨C, hC⟩ := almostPrime_count_le_erdos_sarkozy
  have h : (almostPrimeCounting (k + 1) 1 : ℝ) ≤ 0 := by
    simpa using hC k hk 1 le_rfl
  exact Nat.le_zero.mp (by exact_mod_cast h)

-- The only semiprime up to 4.5 is 4; there are none up to 3.5.
example : almostPrimeCounting 2 ⌊(7 / 2 : ℝ)⌋₊ = 0 := by
  rw [show ⌊(7 / 2 : ℝ)⌋₊ = 3 by exact (Nat.floor_eq_iff (by norm_num)).2 (by norm_num),
    almostPrimeCounting_eq_card_filter]
  decide +kernel

example : almostPrimeCounting 2 ⌊(9 / 2 : ℝ)⌋₊ = 1 := by
  rw [show ⌊(9 / 2 : ℝ)⌋₊ = 4 by exact (Nat.floor_eq_iff (by norm_num)).2 (by norm_num),
    almostPrimeCounting_eq_card_filter]
  decide +kernel

-- The count of integers with exactly three prime factors jumps at 8 = 2³.
example : almostPrimeCounting 3 ⌊(15 / 2 : ℝ)⌋₊ = 0 := by
  rw [show ⌊(15 / 2 : ℝ)⌋₊ = 7 by exact (Nat.floor_eq_iff (by norm_num)).2 (by norm_num),
    almostPrimeCounting_eq_card_filter]
  decide +kernel

example : almostPrimeCounting 3 ⌊(17 / 2 : ℝ)⌋₊ = 1 := by
  rw [show ⌊(17 / 2 : ℝ)⌋₊ = 8 by exact (Nat.floor_eq_iff (by norm_num)).2 (by norm_num),
    almostPrimeCounting_eq_card_filter]
  decide +kernel

-- These larger cutoffs include odd prime powers and mixed prime factorizations.
example : almostPrimeCounting 2 ⌊(21 / 2 : ℝ)⌋₊ = 4 := by
  rw [show ⌊(21 / 2 : ℝ)⌋₊ = 10 by exact (Nat.floor_eq_iff (by norm_num)).2 (by norm_num),
    almostPrimeCounting_eq_card_filter]
  decide +kernel

private theorem count_three_at_55_div_two : almostPrimeCounting 3 ⌊(55 / 2 : ℝ)⌋₊ = 5 := by
  rw [show ⌊(55 / 2 : ℝ)⌋₊ = 27 by exact (Nat.floor_eq_iff (by norm_num)).2 (by norm_num),
    almostPrimeCounting_eq_card_filter]
  decide +kernel

-- Apply the uniform bound at a cutoff with a positive, independently computed count.
example : ∃ C : ℝ, 5 ≤ C * 4 * (55 / 2) * Real.log (55 / 2) := by
  obtain ⟨C, hC⟩ := almostPrime_count_le_erdos_sarkozy
  refine ⟨C, ?_⟩
  have h4 : (2 : ℝ) ^ 4 / 2 ^ (2 : ℕ) = 4 := by norm_num
  simpa only [Nat.reduceAdd, count_three_at_55_div_two, Nat.cast_ofNat, h4] using
    hC 2 (by decide) (55 / 2) (by norm_num)

end MetaMathlibExt
