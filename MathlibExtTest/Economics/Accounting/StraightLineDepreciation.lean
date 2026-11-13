/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Accounting.StraightLineDepreciation
import Mathlib.Tactic.NormNum

@[expose] public section

namespace MathlibExtTest.Economics.Accounting.StraightLineDepreciation

open MathlibExt.Economics.Accounting

/-- Cost 1000, salvage 100, life 3: the charge is 300. -/
theorem test_straightLineCharge : straightLineCharge 1000 100 3 = 300 := by
  unfold straightLineCharge
  norm_num

/-- Book value after one of three periods is 700. -/
theorem test_straightLineBookValue_one : straightLineBookValue 1000 100 3 1 = 700 := by
  unfold straightLineBookValue
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  unfold straightLineCharge
  norm_num

/-- Book value after the full three-period life is the salvage value 100. -/
theorem test_straightLineBookValue_three : straightLineBookValue 1000 100 3 3 = 100 := by
  unfold straightLineBookValue
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  unfold straightLineCharge
  norm_num

/-- With life 0 the sum of charges is empty, so the positive-life hypothesis is needed. -/
theorem test_zero_life :
    ∑ _t ∈ Finset.range 0, straightLineCharge 1000 100 0 ≠ (1000 : ℝ) - 100 := by
  rw [Finset.sum_range_zero]
  norm_num

/-- For every positive life `n`, the `n` charges sum to cost minus salvage, by `sum_straightLineCharge`. -/
theorem test_sum_charges_any_life :
    ∀ n : ℕ, 0 < n → ∑ _t ∈ Finset.range n, straightLineCharge 1000 100 n = 900 := by
  intro n hn
  have h := sum_straightLineCharge 1000 100 hn
  rw [h]
  norm_num

/-- For every positive life `n`, book value at the end of the life is salvage, by `straightLineBookValue_life`. -/
theorem test_bookValue_any_life :
    ∀ n : ℕ, 0 < n → straightLineBookValue 1000 100 n n = 100 := by
  intro n hn
  exact straightLineBookValue_life 1000 100 hn

/-- Charges stop after the useful life: four periods into a three-period life, book value is
still the salvage value 100 (not 1000 - 4 * 300 = -200). -/
theorem test_bookValue_after_life : straightLineBookValue 1000 100 3 4 = 100 := by
  exact straightLineBookValue_of_life_le 1000 100 (by norm_num) (by norm_num)

/-- After the life, book value stays at salvage for every later period, by
`straightLineBookValue_of_life_le`. -/
theorem test_bookValue_after_life_any :
    ∀ t : ℕ, 3 ≤ t → straightLineBookValue 1000 100 3 t = 100 := by
  intro t ht
  exact straightLineBookValue_of_life_le 1000 100 (by norm_num) ht

end MathlibExtTest.Economics.Accounting.StraightLineDepreciation
