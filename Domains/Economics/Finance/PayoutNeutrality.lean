/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Payout accounting identities for dividends and repurchases

A firm with `N` shares at price `P` pays out cash `C`. Two price conventions give the
total shareholder wealth after the payout:

* dividend (`dividendTotal`): `C + N * (P - C / N)`, the cash paid plus the ex-dividend
  market value, with the ex-dividend price taken to be `P - C / N`;
* repurchase (`repurchaseTotal`): `C + (N - C / P) * P`, the cash paid plus the market value
  of the remaining shares, with the repurchase taken to execute at the pre-payout price `P`.

These conventions build the frictionless assumptions of Miller and Modigliani (no taxes, fees,
price impact, or signalling) into the definitions, so each total equals `N * P` by algebra
alone (for nonzero `N`, respectively `P`). The results below are those arithmetic identities,
with nonnegativity side conditions for a feasible payout `0 ≤ C ≤ N * P`. They do not derive
payout neutrality from a valuation model of the firm.

## Main results

* `MathlibExt.Economics.Finance.PayoutNeutrality.dividendTotal_identity`: for `0 < N` and a
  feasible payout, `dividendTotal N P C = N * P`, and the ex-dividend price `P - C / N` is
  nonnegative.
* `MathlibExt.Economics.Finance.PayoutNeutrality.repurchaseTotal_identity`: for `0 < P` and a
  feasible payout, `repurchaseTotal N P C = N * P`, and the remaining share count `N - C / P`
  is nonnegative.
* `MathlibExt.Economics.Finance.PayoutNeutrality.dividendTotal_eq_repurchaseTotal`: for
  `0 < N`, `0 < P`, and a feasible payout, the two totals agree.

## References

M. H. Miller and F. Modigliani, "Dividend Policy, Growth, and the Valuation of
Shares", Journal of Business 34(4), 1961, for the frictionless setting these conventions
follow. Atlas roadmap target FI09.T04.
-/

@[expose] public section

namespace MathlibExt.Economics.Finance.PayoutNeutrality

/-- Total shareholder wealth under a cash dividend: the cash `C` paid out plus the
ex-dividend market value, with the ex-dividend price taken to be `P - C / N`. This price
convention encodes the frictionless assumption (no taxes, fees, or signalling), and with it
the total is `N * P` whenever `N ≠ 0` (`dividendTotal_identity`). -/
noncomputable def dividendTotal (N P C : ℝ) : ℝ :=
  C + N * (P - C / N)

/-- Total shareholder wealth under a share repurchase: the cash `C` paid to selling
shareholders plus the market value of the `N - C / P` remaining shares, with the
repurchase taken to execute at the pre-payout price `P`. This price convention encodes the
frictionless assumption (no taxes, fees, price impact, or signalling), and with it the total
is `N * P` whenever `P ≠ 0` (`repurchaseTotal_identity`). -/
noncomputable def repurchaseTotal (N P C : ℝ) : ℝ :=
  C + (N - C / P) * P

/-- Dividend accounting identity: under the price convention of `dividendTotal`, the
total is `N * P` (an algebraic identity), and for a feasible payout `0 ≤ C ≤ N * P` the
ex-dividend price `P - C / N` is nonnegative. -/
theorem dividendTotal_identity {N P C : ℝ} (hN : 0 < N) (hC0 : 0 ≤ C) (hC : C ≤ N * P) :
    dividendTotal N P C = N * P ∧ 0 ≤ P - C / N := by
  have hN' : N ≠ 0 := ne_of_gt hN
  constructor
  · unfold dividendTotal
    field_simp
    ring
  · rw [sub_nonneg, div_le_iff₀ hN, mul_comm P N]
    exact hC

/-- Repurchase accounting identity: under the price convention of `repurchaseTotal`, the
total is `N * P` (an algebraic identity), and for a feasible payout `0 ≤ C ≤ N * P` the
remaining share count `N - C / P` is nonnegative. -/
theorem repurchaseTotal_identity {N P C : ℝ} (hP : 0 < P) (hC0 : 0 ≤ C)
    (hC : C ≤ N * P) :
    repurchaseTotal N P C = N * P ∧ 0 ≤ N - C / P := by
  have hP' : P ≠ 0 := ne_of_gt hP
  constructor
  · unfold repurchaseTotal
    field_simp
    ring
  · rw [sub_nonneg, div_le_iff₀ hP]
    exact hC

/-- The two payout conventions give the same total: for a feasible payout
`0 ≤ C ≤ N * P`, both `dividendTotal N P C` and `repurchaseTotal N P C` equal `N * P`. -/
theorem dividendTotal_eq_repurchaseTotal {N P C : ℝ} (hN : 0 < N) (hP : 0 < P) (hC0 : 0 ≤ C)
    (hC : C ≤ N * P) :
    dividendTotal N P C = repurchaseTotal N P C := by
  have h1 := (dividendTotal_identity hN hC0 hC).1
  have h2 := (repurchaseTotal_identity hP hC0 hC).1
  rw [h1, h2]

end MathlibExt.Economics.Finance.PayoutNeutrality
