/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Finance.Annuity
import Mathlib.Tactic.NormNum

/-!
# Tests for the level annuity

`a_2 = 3/4` at `r = 1` (direct and via the closed form), `a_2 = 6` at `r = -1/2`, the
zero-rate branch `a_5 = 5`, and `a_0 = 0`.
-/

@[expose] public section

namespace MathlibExtTest.Economics.Finance.Annuity

open MathlibExt.Economics.Finance

-- Test section (required): concrete evaluations with all hypotheses proved.

/-- Direct computation: `a_2` at 100% is `1/2 + 1/4`. -/
example : MathlibExt.Economics.Finance.annuityImmediate 1 2 = 3 / 4 := by
  simp only [MathlibExt.Economics.Finance.annuityImmediate,
    MathlibExt.Economics.Finance.presentValue]
  have hIcc12 : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  have h12 : (1:ℕ) ∉ ({2} : Finset ℕ) := by decide
  rw [hIcc12, Finset.sum_insert h12, Finset.sum_singleton]
  simp only [MathlibExt.Economics.Finance.discountFactor, mul_one]
  norm_num

/-- Same value via the closed form. -/
example : MathlibExt.Economics.Finance.annuityImmediate 1 2 = 3 / 4 := by
  rw [MathlibExt.Economics.Finance.annuityImmediate_eq_of_ne_zero 1 2
    (by norm_num) (by norm_num)]
  norm_num

/-- Negative rate above `-1`: `1 + r = 1/2`, so `a_2 = 2 + 4`. -/
example : MathlibExt.Economics.Finance.annuityImmediate (-1/2) 2 = 6 := by
  rw [MathlibExt.Economics.Finance.annuityImmediate_eq_of_ne_zero _ _
    (by norm_num) (by norm_num)]
  norm_num

/-- Zero rate: `a_5 = 5`. -/
example : MathlibExt.Economics.Finance.annuityImmediate 0 5 = 5 := by
  rw [MathlibExt.Economics.Finance.annuityImmediate_zero_rate]
  norm_num

/-- Empty annuity is worthless at any rate. -/
example (r : ℝ) : MathlibExt.Economics.Finance.annuityImmediate r 0 = 0 := by
  simp [MathlibExt.Economics.Finance.annuityImmediate,
    MathlibExt.Economics.Finance.presentValue]

end MathlibExtTest.Economics.Finance.Annuity
