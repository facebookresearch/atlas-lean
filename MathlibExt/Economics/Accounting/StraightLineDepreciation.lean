/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic

@[expose] public section

/-!
# Straight-line depreciation (Atlas AC02.T01)

Straight-line depreciation charges `(cost - salvage) / life` per period. Over a
positive useful life the charges sum to `cost - salvage` (`Finset.sum_const` and
`mul_div_cancel₀`), so book value at the end of the life equals salvage.

## Main results

* `MathlibExt.Economics.Accounting.sum_straightLineCharge`
* `MathlibExt.Economics.Accounting.straightLineBookValue_life`

## References

* OpenStax, *Principles of Accounting, Volume 1: Financial Accounting*, §11.3
  (depreciation methods).
-/

namespace MathlibExt.Economics.Accounting

/-- Straight-line depreciation charge per period: `(cost - salvage) / life`. -/
noncomputable def straightLineCharge (cost salvage : ℝ) (life : ℕ) : ℝ :=
  (cost - salvage) / life

/-- Book value after `t` periods of straight-line depreciation. -/
noncomputable def straightLineBookValue (cost salvage : ℝ) (life t : ℕ) : ℝ :=
  cost - ∑ _s ∈ Finset.range t, straightLineCharge cost salvage life

/-- Over a positive useful life, straight-line charges sum to cost minus salvage. -/
theorem sum_straightLineCharge (cost salvage : ℝ) {life : ℕ} (hlife : 0 < life) :
    ∑ _t ∈ Finset.range life, straightLineCharge cost salvage life = cost - salvage := by
  unfold straightLineCharge
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hlife' : (life : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hlife
  exact mul_div_cancel₀ _ hlife'

/-- At the end of a positive useful life, straight-line book value equals salvage. -/
theorem straightLineBookValue_life (cost salvage : ℝ) {life : ℕ} (hlife : 0 < life) :
    straightLineBookValue cost salvage life life = salvage := by
  unfold straightLineBookValue
  rw [sum_straightLineCharge cost salvage hlife, sub_sub_cancel]

end MathlibExt.Economics.Accounting
