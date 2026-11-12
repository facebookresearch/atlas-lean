/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Finance.LawOfOnePrice
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Tests for the law of one price

* A two-state, two-asset market with a redundant asset (`X 0 = X 1 = ![4, 0]`,
  priced by `ψ = ![1/2, 1/2]` at `p = ![2, 2]`): the holdings `![1, 0]` and
  `![0, 1]` have equal payoffs and equal prices.
-/

@[expose] public section

namespace MathlibExtTest.Probability.Finance.LawOfOnePrice

open MathlibExt.Probability.Finance.LawOfOnePrice in
/-- Concrete test: two states, two assets with a redundant asset. -/
example : (∑ a : Fin 2, (![1, 0] : Fin 2 → ℝ) a * (![2, 2] : Fin 2 → ℝ) a)
    = (∑ a : Fin 2, (![0, 1] : Fin 2 → ℝ) a * (![2, 2] : Fin 2 → ℝ) a) := by
  have hprice : ∀ a : Fin 2, (![2, 2] : Fin 2 → ℝ) a
      = ∑ ω : Fin 2, (![1/2, 1/2] : Fin 2 → ℝ) ω * (![4, 0] : Fin 2 → ℝ) ω := by
    intro a
    fin_cases a <;> simp [Fin.sum_univ_two] <;> norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  have hpay : ∀ ω : Fin 2, ∑ a : Fin 2, (![1, 0] : Fin 2 → ℝ) a * (![4, 0] : Fin 2 → ℝ) ω
      = ∑ a : Fin 2, (![0, 1] : Fin 2 → ℝ) a * (![4, 0] : Fin 2 → ℝ) ω := by
    intro ω
    fin_cases ω <;> simp [Fin.sum_univ_two]
  exact law_of_one_price (fun _ => (![4, 0] : Fin 2 → ℝ)) (![2, 2] : Fin 2 → ℝ)
    (![1/2, 1/2] : Fin 2 → ℝ) hprice hpay

open MathlibExt.Probability.Finance.LawOfOnePrice

namespace RedundantAssetTest

open Matrix

/-- Redundant-asset market: both assets pay `![4, 0]`, both cost `1`, `R = 2`. -/
def Xtest : Fin 2 → Fin 2 → ℝ := fun _ => ![4, 0]
def ptest : Fin 2 → ℝ := ![1, 1]

/-- No funded arbitrage: funded gains are `[2, -2]` per unit of `h 0 + h 1`,
so nonnegativity in both states forces both gains to `0`. -/
theorem noArb_test :
    MathlibExt.Probability.Finance.StatePriceVector.NoFundedArbitrage Xtest ptest 2 := by
  rintro ⟨h, hnonneg, ω, hpos⟩
  have h0 := hnonneg 0
  have h1 := hnonneg 1
  fin_cases ω <;>
    simp only [Xtest, ptest, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Fin.mk_zero, Fin.mk_one] at h0 h1 hpos <;>
    norm_num at h0 h1 hpos <;>
    linarith

/-- Law of one price applied to holdings `![1, 0]` and `![0, 1]`. -/
theorem price_test :
    ∑ a : Fin 2, ![1, 0] a * ptest a = ∑ a : Fin 2, ![0, 1] a * ptest a := by
  apply law_of_one_price_of_no_arbitrage Xtest ptest 2 (by norm_num) noArb_test
  intro ω
  simp only [Xtest, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    one_mul, zero_mul, add_zero, zero_add]

end RedundantAssetTest

end MathlibExtTest.Probability.Finance.LawOfOnePrice
