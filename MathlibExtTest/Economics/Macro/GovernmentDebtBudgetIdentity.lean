/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Macro.GovernmentDebtBudgetIdentity
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

@[expose] public section

namespace MathlibExtTest.Economics.Macro.GovernmentDebtBudgetIdentity

open MathlibExt.Economics.Finance MathlibExt.Economics.Macro.GovernmentDebtBudgetIdentity

/-- Concrete budget identity: interest rate `r = 1`, initial debt `100`, primary
deficits `D 1 = 10`, `D 2 = 20`. Then `B 1 = 210`, `B 2 = 440`, and
`100 + 10 / 2 + 20 / 4 = 440 / 4 = 110`. Prove by deriving `B 2 = 440` from the
recursion and applying `governmentBudgetIdentity` at `n = 2`. -/
theorem governmentDebt_example {B D : ℕ → ℝ} (h : DebtRecursion B D 1)
    (hB : B 0 = 100) (hD1 : D 1 = 10) (hD2 : D 2 = 20) :
    B 2 = 440 ∧ B 0 + (D 1 / 2 + D 2 / 4) = B 2 / 4 := by
  have h0 := h 0
  have h1 := h 1
  norm_num at h0 h1
  rw [hB, hD1] at h0
  norm_num at h0
  rw [h0, hD2] at h1
  norm_num at h1
  have hsum : ∑ s ∈ Finset.Icc 1 2, D s / (1 + 1 : ℝ) ^ s = D 1 / 2 + D 2 / 4 := by
    rw [Finset.sum_Icc_succ_top (by norm_num : 1 ≤ 1 + 1) _]
    rw [Finset.Icc_self, Finset.sum_singleton]
    norm_num
  have hmain := governmentBudgetIdentity h (by norm_num : (1 + (1 : ℝ)) ≠ 0) 2
  rw [hsum] at hmain
  norm_num at hmain
  exact ⟨h1, hmain⟩

/-- The same data in the canonical present-value form: the present value of the deficits
is `presentValue (discountFactor 1) (Finset.Icc 1 2) D = 10 / 2 + 20 / 4 = 10`, and by
`governmentBudgetIdentity_presentValue` the discounted terminal debt is
`discountFactor 1 2 * B 2 = 100 + 10 = 110`. -/
theorem governmentDebt_presentValue_example {B D : ℕ → ℝ} (h : DebtRecursion B D 1)
    (hB : B 0 = 100) (hD1 : D 1 = 10) (hD2 : D 2 = 20) :
    presentValue (discountFactor 1) (Finset.Icc 1 2) D = 10 ∧
      discountFactor 1 2 * B 2 = 110 := by
  have hpv : presentValue (discountFactor 1) (Finset.Icc 1 2) D = 10 := by
    rw [presentValue, Finset.sum_Icc_succ_top (by norm_num : 1 ≤ 1 + 1) _]
    rw [Finset.Icc_self, Finset.sum_singleton]
    norm_num [discountFactor, hD1, hD2]
  have hmain := governmentBudgetIdentity_presentValue h (by norm_num : (1 + (1 : ℝ)) ≠ 0) 2
  rw [hpv, hB] at hmain
  exact ⟨hpv, by linarith⟩

/-- Concrete zero-deficit case: with no primary deficits, debt compounds at the interest
rate, `B 2 = 4 * B 0` at `r = 1`. Prove from the recursion (two steps). -/
theorem governmentDebt_zeroDeficit_example {B D : ℕ → ℝ} (h : DebtRecursion B D 1)
    (hD : ∀ t, D t = 0) : B 2 = 4 * B 0 := by
  have h0 := h 0
  have h1 := h 1
  norm_num at h0 h1
  rw [hD 1] at h0
  rw [hD 2] at h1
  rw [h0] at h1
  linarith

end MathlibExtTest.Economics.Macro.GovernmentDebtBudgetIdentity
