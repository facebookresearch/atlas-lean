/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ConsecutivePrimePowerSums

open Finset MetaMathlibExt

-- For a single term, an exact kth power gives an inclusive prime-counting cutoff.
example (k p : ℕ) (hk : 1 < k) :
    {n : ℕ | n ≤ p ^ k ∧ ∃ l, n = Nat.nth Nat.Prime l ^ k}.ncard ≤ p.primeCounting := by
  simpa [one_div, Real.pow_rpow_inv_natCast (Nat.cast_nonneg p) (Nat.ne_zero_of_lt hk)]
    using card_consecutivePrimePowerSums_length_le k 1 (p ^ k) hk (by decide)

-- The first two prime squares sum to 13, and the bound counts just one possible start.
example :
    {n : ℕ | n ≤ 13 ∧ ∃ l, n = ∑ i ∈ range 2, Nat.nth Nat.Prime (l + i) ^ 2}.ncard = 1 := by
  apply le_antisymm
  · have h := card_consecutivePrimePowerSums_length_le 2 2 13 (by decide) (by decide)
    have hcut : ⌊((13 : ℝ) / 2) ^ ((1 : ℝ) / 2)⌋₊ < 3 := by
      rw [Nat.floor_lt (by positivity), one_div, Real.rpow_inv_lt_iff_of_pos (by positivity)
        (by positivity) (by norm_num)]
      norm_num
    exact h.trans ((Nat.monotone_primeCounting (Nat.le_of_lt_succ hcut)).trans (by decide))
  · refine (Set.ncard_pos ?_).mpr ⟨13, le_rfl, 0, ?_⟩
    · exact (Set.finite_Iic 13).subset fun _ hn ↦ hn.1
    · norm_num [sum_range_succ, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three]
