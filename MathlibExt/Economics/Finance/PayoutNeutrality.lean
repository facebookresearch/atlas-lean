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
# Payout neutrality: dividends and repurchases preserve shareholder wealth

Paying out cash `C` as a dividend or as a share repurchase preserves total
shareholder wealth at `N * P` under exact funding assumptions. The dividend
construction is `C + N * (P - C / N)`: the per-share price falls by exactly the
dividend per share. The repurchase construction is `C + (N - C / P) * P`: the
repurchase executes at the pre-payout price `P`. Both assume no taxes, fees,
price impact, or signalling, and a feasible payout `0 ≤ C ≤ N * P`.

## Main results

* `MathlibExt.Economics.Finance.PayoutNeutrality.dividend_neutrality`: a
  dividend preserves total wealth, and the ex-dividend price stays nonnegative.
* `MathlibExt.Economics.Finance.PayoutNeutrality.repurchase_neutrality`: a
  repurchase preserves total wealth, and the remaining share count stays
  nonnegative.
* `MathlibExt.Economics.Finance.PayoutNeutrality.payout_form_neutrality`: the
  two payout forms leave total wealth equal.

## References

M. H. Miller and F. Modigliani, "Dividend Policy, Growth, and the Valuation of
Shares", Journal of Business 34(4), 1961. Atlas roadmap target FI09.T04.
-/

@[expose] public section

namespace MathlibExt.Economics.Finance.PayoutNeutrality

/-- Total shareholder wealth under a cash dividend: the cash `C` paid out plus the
ex-dividend market value, where the per-share price falls by exactly the dividend
per share `C / N` (frictionless funding assumption: no taxes, fees, or signalling). -/
noncomputable def dividendTotal (N P C : ℝ) : ℝ :=
  C + N * (P - C / N)

/-- Total shareholder wealth under a share repurchase: the cash `C` paid to selling
shareholders plus the market value of the remaining shares, where the repurchase
executes at the pre-payout price `P` (frictionless funding assumption: no taxes,
fees, price impact, or signalling). -/
noncomputable def repurchaseTotal (N P C : ℝ) : ℝ :=
  C + (N - C / P) * P

/-- Dividend neutrality: a dividend preserves total shareholder wealth at `N * P`,
and the ex-dividend price stays nonnegative when the payout is feasible
(`C ≤ N * P`). -/
theorem dividend_neutrality {N P C : ℝ} (hN : 0 < N) (hC : C ≤ N * P) :
    dividendTotal N P C = N * P ∧ 0 ≤ P - C / N := by
  have hN' : N ≠ 0 := ne_of_gt hN
  constructor
  · unfold dividendTotal
    field_simp
    ring
  · rw [sub_nonneg, div_le_iff₀ hN, mul_comm P N]
    exact hC

/-- Repurchase neutrality: a repurchase at price `P` preserves total shareholder
wealth at `N * P`, and the share count left after the repurchase stays nonnegative
when the payout is feasible (`0 ≤ C ≤ N * P`). -/
theorem repurchase_neutrality {N P C : ℝ} (hP : 0 < P) (hC0 : 0 ≤ C)
    (hC : C ≤ N * P) :
    repurchaseTotal N P C = N * P ∧ 0 ≤ N - C / P := by
  have hP' : P ≠ 0 := ne_of_gt hP
  constructor
  · unfold repurchaseTotal
    field_simp
    ring
  · rw [sub_nonneg, div_le_iff₀ hP]
    exact hC

/-- Payout-form neutrality: under the exact funding assumptions above, a dividend
and a repurchase of the same cash amount `C` leave total shareholder wealth equal,
so the form of the payout does not create or destroy wealth. -/
theorem payout_form_neutrality {N P C : ℝ} (hN : 0 < N) (hP : 0 < P) (hC0 : 0 ≤ C)
    (hC : C ≤ N * P) :
    dividendTotal N P C = repurchaseTotal N P C := by
  have h1 := (dividend_neutrality hN hC).1
  have h2 := (repurchase_neutrality hP hC0 hC).1
  rw [h1, h2]

end MathlibExt.Economics.Finance.PayoutNeutrality
