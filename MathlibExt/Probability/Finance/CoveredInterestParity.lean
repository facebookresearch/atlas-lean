/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Covered interest parity

A one-period two-currency market: the domestic deposit and the converted
foreign deposit plus forward replicate the same terminal domestic payoff.
Covered interest parity is the resulting forward-rate formula.

## Main results

* `coveredInterestParity_iff`: the replication equality iff
  `forward = spot * domesticGross / foreignGross`.
* `coveredInterestParity_example`: a concrete instance.
-/

@[expose] public section

namespace MathlibExt.Probability.Finance.CoveredInterestParity

/-- A one-period two-currency market for covered interest parity.

* `spot`: spot exchange rate, domestic currency per one unit of foreign currency.
* `forward`: forward exchange rate for the same quotation (domestic per foreign).
* `domesticGross`: gross domestic return over the period (`1 + r_d`).
* `foreignGross`: gross foreign return over the period (`1 + r_f`).

All four are period gross quantities; no interest-rate sign assumption is made. -/
structure CoveredInterestMarket where
  /-- Spot rate: domestic currency per one unit of foreign currency. -/
  spot : ℝ
  /-- Forward rate: domestic currency per one unit of foreign currency. -/
  forward : ℝ
  /-- Gross domestic return over the period. -/
  domesticGross : ℝ
  /-- Gross foreign return over the period. -/
  foreignGross : ℝ

/-- Terminal domestic payoff of investing one unit of domestic currency at the
domestic gross return: `domesticGross`. -/
noncomputable def domesticDepositPayoff (M : CoveredInterestMarket) : ℝ :=
  M.domesticGross

/-- Terminal domestic payoff of the replicating strategy: convert one unit of
domestic currency to `1 / spot` units of foreign currency, invest at the foreign
gross return, and convert the proceeds back at the locked-in forward rate:
`forward * foreignGross / spot`. -/
noncomputable def convertedForeignPayoff (M : CoveredInterestMarket) : ℝ :=
  M.forward * M.foreignGross / M.spot

/-- Covered interest parity: the replicating strategy has the same terminal
domestic payoff as the domestic deposit iff the forward rate is
`spot * domesticGross / foreignGross`. -/
theorem coveredInterestParity_iff (M : CoveredInterestMarket)
    (hS : M.spot ≠ 0) (hRf : M.foreignGross ≠ 0) :
    convertedForeignPayoff M = domesticDepositPayoff M ↔
      M.forward = M.spot * M.domesticGross / M.foreignGross := by
  unfold convertedForeignPayoff domesticDepositPayoff
  rw [div_eq_iff hS, eq_div_iff hRf]
  constructor <;> intro h <;> ring_nf at h ⊢ <;> exact h

/-- Concrete covered-interest-parity instance: spot `6/5`, domestic gross
`21/20`, foreign gross `51/50`, forward `21/17`. -/
theorem coveredInterestParity_example :
    convertedForeignPayoff ⟨6 / 5, 21 / 17, 21 / 20, 51 / 50⟩ =
      domesticDepositPayoff ⟨6 / 5, 21 / 17, 21 / 20, 51 / 50⟩ := by
  unfold convertedForeignPayoff domesticDepositPayoff
  norm_num

end MathlibExt.Probability.Finance.CoveredInterestParity
