/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Exchange.WalrasLaw
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases

@[expose] public section

open MathlibExt.Economics MathlibExt.Economics.ExchangeEquilibriumExistence MathlibExt.Economics.ExchangeEquilibriumExistence.ExchangeEconomy

namespace MathlibExtTest.Economics.Exchange.WalrasLaw

namespace WalrasLawExamples

/-- Two consumers, two goods; consumer `0` owns good `0`, consumer `1` owns good `1`, and both
demand one unit of good `1` at every price. -/
def overdemand : ExchangeEconomy (Fin 2) (Fin 2) where
  endowment := ![![1, 0], ![0, 1]]
  demand := fun _ _ => ![0, 1]

theorem overdemand_excessDemand : overdemand.excessDemand ![1, 1] = ![-1, 1] := by
  ext i
  fin_cases i <;> simp [overdemand, ExchangeEconomy.excessDemand, Fin.sum_univ_two]
  norm_num

/-- At prices `(1, 1)` both budgets bind and Walras' law holds, although good `1` is in excess
demand. -/
theorem overdemand_walras : (![1, 1] : Fin 2 → ℝ) ⬝ᵥ overdemand.excessDemand ![1, 1] = 0 := by
  apply dotProduct_excessDemand_eq_zero
  intro i
  fin_cases i <;> simp [overdemand, dotProduct, Fin.sum_univ_two]

/-- Consumer `0` demands nothing and leaves wealth unspent: Walras' law fails. -/
def underspend : ExchangeEconomy (Fin 2) (Fin 2) where
  endowment := ![![1, 0], ![0, 1]]
  demand := ![fun _ => ![0, 0], fun _ => ![0, 1]]

theorem underspend_not_walras :
    (![1, 1] : Fin 2 → ℝ) ⬝ᵥ underspend.excessDemand ![1, 1] ≠ 0 := by
  have h : underspend.excessDemand ![1, 1] = ![-1, 0] := by
    ext i
    fin_cases i <;> simp [underspend, ExchangeEconomy.excessDemand, Fin.sum_univ_two]
  rw [h]
  simp [dotProduct, Fin.sum_univ_two]

end WalrasLawExamples

end MathlibExtTest.Economics.Exchange.WalrasLaw
