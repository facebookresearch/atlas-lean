/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Finance.BondPrice
import Mathlib.Tactic.NormNum

/-!
# Tests for bond price

A bond with coupon `5`, face `100`, maturity `2` at rate `1` costs `115 / 4`
(`5/2 + 105/4`); with maturity `1` it costs `105 / 2`.
-/

@[expose] public section

namespace MathlibExtTest.Economics.Finance.BondPrice

open MathlibExt.Economics.Finance

-- Test section (required): concrete evaluations with all hypotheses proved.

/-- Coupon `5`, face `100`, maturity `2`, rate `1`: `5/2 + 105/4 = 115/4`. -/
example : bondPrice 5 100 2 1 = 115 / 4 := by
  have h := bondPrice_eq_coupon_plus_redemption 5 100
    (show 1 ≤ 2 by norm_num) 1
  rw [h]
  have hIcc : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  rw [hIcc]
  simp only [Finset.sum_insert (by decide : (1 : ℕ) ∉ ({2} : Finset ℕ)),
    Finset.sum_singleton]
  unfold discountFactor
  norm_num

/-- Coupon `5`, face `100`, maturity `1`, rate `1`: `(5 + 100) / 2 = 105 / 2`. -/
example : bondPrice 5 100 1 1 = 105 / 2 := by
  have h := bondPrice_eq_coupon_plus_redemption 5 100
    (show 1 ≤ 1 by norm_num) 1
  rw [h]
  have hIcc : Finset.Icc 1 1 = ({1} : Finset ℕ) := by decide
  rw [hIcc, Finset.sum_singleton]
  unfold discountFactor
  norm_num

end MathlibExtTest.Economics.Finance.BondPrice
