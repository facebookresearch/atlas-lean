/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.VecNotation
public import MathlibExt.Probability.Finance.StatePriceVector
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Covered interest parity

A one-period two-currency market with two ways to invest one unit of domestic
currency: the domestic deposit, and the covered foreign strategy (convert at the
spot rate, deposit abroad, and sell the foreign proceeds forward). When the
domestic deposit, the foreign deposit and the forward trade as three assets in a
finite one-period market with an arbitrary terminal spot rate, no arbitrage
forces covered interest parity, `forward * foreignGross = spot * domesticGross`:
the covered foreign strategy pays `forward * foreignGross` in every state at
cost `spot`, and the strictly positive state prices that no arbitrage supplies
(FI08.T02, `exists_statePriceVector_prices_replicated`) must value it
consistently with the domestic deposit.

## Main results

* `forward_mul_foreignGross_eq_of_noFundedArbitrage`: no arbitrage on funded
  gains forces `forward * foreignGross = spot * domesticGross`.
* `coveredInterestParity_of_noFundedArbitrage`, `forward_eq_of_noFundedArbitrage`:
  under no arbitrage the two payoffs are equal (nonzero spot rate) and
  `forward = spot * domesticGross / foreignGross` (nonzero foreign gross return).
* `coveredInterestParity_iff`: the algebra relating the payoff form and the rate
  form: for a nonzero spot rate and foreign gross return, the two payoffs are
  equal iff `forward = spot * domesticGross / foreignGross`.
* `coveredInterestParity_example`: a concrete instance.
-/

@[expose] public section

namespace MathlibExt.Probability.Finance.CoveredInterestParity

open MathlibExt.Probability.Finance.StatePriceVector

/-- A one-period two-currency market for covered interest parity.

* `spot`: spot exchange rate, domestic currency per one unit of foreign currency.
* `forward`: forward exchange rate for the same quotation (domestic per foreign).
* `domesticGross`: gross domestic return over the period (`1 + r_d`).
* `foreignGross`: gross foreign return over the period (`1 + r_f`).

`spot` and `forward` are exchange rates in domestic currency per unit of foreign
currency; `domesticGross` and `foreignGross` are dimensionless gross returns. No
interest-rate sign assumption is made. -/
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

/-- Terminal domestic payoff of the covered foreign strategy: convert one unit of
domestic currency to `1 / spot` units of foreign currency, invest at the foreign
gross return, and convert the proceeds back at the locked-in forward rate:
`forward * foreignGross / spot`. For nonzero `spot` and `foreignGross` it equals
the domestic deposit payoff only when covered interest parity holds
(`coveredInterestParity_iff`). -/
noncomputable def convertedForeignPayoff (M : CoveredInterestMarket) : ℝ :=
  M.forward * M.foreignGross / M.spot

/-- Payoff form and rate form of covered interest parity agree: the covered
foreign strategy has the same terminal domestic payoff as the domestic deposit
iff the forward rate is `spot * domesticGross / foreignGross`. This is algebra
about the four rates; `coveredInterestParity_of_noFundedArbitrage` derives the
payoff equality from no arbitrage. -/
theorem coveredInterestParity_iff (M : CoveredInterestMarket)
    (hS : M.spot ≠ 0) (hRf : M.foreignGross ≠ 0) :
    convertedForeignPayoff M = domesticDepositPayoff M ↔
      M.forward = M.spot * M.domesticGross / M.foreignGross := by
  unfold convertedForeignPayoff domesticDepositPayoff
  rw [div_eq_iff hS, eq_div_iff hRf]
  constructor <;> intro h <;> ring_nf at h ⊢ <;> exact h

/-- Terminal domestic payoffs of the three traded assets when the spot rate at
the end of the period is `ST ω` in state `ω`: the domestic deposit (asset `0`)
pays `domesticGross`; one unit of foreign currency deposited abroad (asset `1`)
pays `foreignGross` foreign units, worth `foreignGross * ST ω`; a long forward
on one unit of foreign currency (asset `2`) pays `ST ω - forward`. -/
noncomputable def assetPayoff {Ω : Type*} (M : CoveredInterestMarket) (ST : Ω → ℝ) :
    Fin 3 → Ω → ℝ :=
  ![fun _ => M.domesticGross, fun ω => M.foreignGross * ST ω, fun ω => ST ω - M.forward]

/-- Prices of the three traded assets today, in domestic currency: the domestic
deposit costs `1`, one unit of foreign currency costs `spot`, and entering the
forward costs nothing. -/
noncomputable def assetPrice (M : CoveredInterestMarket) : Fin 3 → ℝ :=
  ![1, M.spot, 0]

/-- **Covered interest parity from no arbitrage.** If the market trading the
domestic deposit, the foreign deposit and the forward (`assetPayoff`,
`assetPrice`) admits no arbitrage on funded gains at some gross funding rate
`R > 0`, then `forward * foreignGross = spot * domesticGross`, whatever the
terminal spot rate `ST`. The covered foreign strategy (one unit of foreign
currency, deposited, with `foreignGross` sold forward) pays
`forward * foreignGross` in every state at cost `spot`, and the state prices of
`exists_statePriceVector_prices_replicated` value it consistently with the
domestic deposit. -/
theorem forward_mul_foreignGross_eq_of_noFundedArbitrage {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (M : CoveredInterestMarket) (ST : Ω → ℝ) (R : ℝ) (hR : 0 < R)
    (hNA : NoFundedArbitrage (assetPayoff M ST) (assetPrice M) R) :
    M.forward * M.foreignGross = M.spot * M.domesticGross := by
  obtain ⟨ψ, -, -, hprice⟩ :=
    exists_statePriceVector_prices_replicated (assetPayoff M ST) (assetPrice M) R hR hNA
  -- A portfolio paying the constant `c` in every state costs `(∑ ω, ψ ω) * c`.
  have hconst (h : Fin 3 → ℝ) (c : ℝ) (hc : ∀ ω, ∑ a, h a * assetPayoff M ST a ω = c) :
      (∑ ω, ψ ω) * c = ∑ a, h a * assetPrice M a := by
    rw [← hprice h, Finset.sum_mul]
    exact Finset.sum_congr rfl fun ω _ => by rw [hc ω]
  -- The domestic deposit pays `domesticGross`; the covered foreign strategy pays
  -- `forward * foreignGross`.
  have hdom := hconst ![1, 0, 0] M.domesticGross fun ω => by
    simp only [Fin.sum_univ_three, assetPayoff, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ring
  have hcov := hconst ![0, 1, -M.foreignGross] (M.forward * M.foreignGross) fun ω => by
    simp only [Fin.sum_univ_three, assetPayoff, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ring
  simp only [Fin.sum_univ_three, assetPrice, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hdom hcov
  linear_combination (-(M.forward * M.foreignGross)) * hdom + M.domesticGross * hcov

/-- **Covered interest parity from no arbitrage**, payoff form: for a nonzero
spot rate, no arbitrage makes the covered foreign strategy pay exactly the
domestic deposit payoff. -/
theorem coveredInterestParity_of_noFundedArbitrage {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (M : CoveredInterestMarket) (ST : Ω → ℝ) (R : ℝ) (hR : 0 < R) (hS : M.spot ≠ 0)
    (hNA : NoFundedArbitrage (assetPayoff M ST) (assetPrice M) R) :
    convertedForeignPayoff M = domesticDepositPayoff M := by
  unfold convertedForeignPayoff domesticDepositPayoff
  rw [div_eq_iff hS, forward_mul_foreignGross_eq_of_noFundedArbitrage M ST R hR hNA, mul_comm]

/-- **Covered interest parity from no arbitrage**, rate form: for a nonzero
foreign gross return, no arbitrage forces
`forward = spot * domesticGross / foreignGross`. -/
theorem forward_eq_of_noFundedArbitrage {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (M : CoveredInterestMarket) (ST : Ω → ℝ) (R : ℝ) (hR : 0 < R) (hRf : M.foreignGross ≠ 0)
    (hNA : NoFundedArbitrage (assetPayoff M ST) (assetPrice M) R) :
    M.forward = M.spot * M.domesticGross / M.foreignGross :=
  (eq_div_iff hRf).mpr (forward_mul_foreignGross_eq_of_noFundedArbitrage M ST R hR hNA)

/-- Concrete covered-interest-parity instance: spot `6/5`, domestic gross
`21/20`, foreign gross `51/50`, forward `21/17`. -/
theorem coveredInterestParity_example :
    convertedForeignPayoff ⟨6 / 5, 21 / 17, 21 / 20, 51 / 50⟩ =
      domesticDepositPayoff ⟨6 / 5, 21 / 17, 21 / 20, 51 / 50⟩ := by
  unfold convertedForeignPayoff domesticDepositPayoff
  norm_num

end MathlibExt.Probability.Finance.CoveredInterestParity
