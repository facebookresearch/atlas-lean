/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.MechanismDesign.BilateralTrade
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

open MathlibExt.GameTheory.MechanismDesign.BilateralTrade

example : ¬ ∃ M : BilateralMechanism, Efficient M ∧ BuyerDSIC M ∧ SellerDSIC M ∧
    ExPostIR M ∧ WeaklyBudgetBalanced M :=
  not_exists_efficient_dsic_ir_wbb

-- At reports `(0, 1)` an efficient, DSIC, IR mechanism charges the buyer `0`
-- and pays the seller `1`: the deficit that weak budget balance forbids.
example (M : BilateralMechanism) (hE : Efficient M) (hB : BuyerDSIC M)
    (hS : SellerDSIC M) (hIR : ExPostIR M) :
    M.payBuyer 0 1 = 0 ∧ M.paySeller 0 1 = 1 := by
  have hs : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.mem_Icc.mpr ⟨le_refl 0, zero_le_one⟩
  have hb : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.mem_Icc.mpr ⟨zero_le_one, le_refl 1⟩
  exact ⟨payBuyer_eq_of_lt M hE hB hIR hs hb zero_lt_one,
    paySeller_eq_of_lt M hE hS hIR hs hb zero_lt_one⟩

-- The posted-price mechanism at `1/2` passes every requirement but efficiency.
example : BuyerDSIC (postedPrice (1 / 2 : ℝ)) ∧ SellerDSIC (postedPrice (1 / 2 : ℝ)) ∧
    ExPostIR (postedPrice (1 / 2 : ℝ)) ∧ WeaklyBudgetBalanced (postedPrice (1 / 2 : ℝ)) ∧
    ¬ Efficient (postedPrice (1 / 2 : ℝ)) := by
  have hp : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
  exact ⟨postedPrice_buyerDSIC hp, postedPrice_sellerDSIC hp, postedPrice_exPostIR hp,
    postedPrice_weaklyBudgetBalanced hp, postedPrice_not_efficient hp⟩

-- Posted-price allocation at `1/2`: trade at `(0, 1)`, no trade at `(3/4, 1)`
-- although `3/4 < 1`, and no trade at `(0, 1/4)` although `0 < 1/4`.
example : (postedPrice (1 / 2 : ℝ)).alloc 0 1 = 1 := by norm_num [postedPrice]

example : (postedPrice (1 / 2 : ℝ)).alloc (3 / 4) 1 = 0 := by norm_num [postedPrice]

example : (postedPrice (1 / 2 : ℝ)).alloc 0 (1 / 4) = 0 := by norm_num [postedPrice]

example (s b : ℝ) : (postedPrice (1 / 2 : ℝ)).payBuyer s b = 1 / 2 ∧
    (postedPrice (1 / 2 : ℝ)).paySeller s b = 1 / 2 :=
  ⟨rfl, rfl⟩
