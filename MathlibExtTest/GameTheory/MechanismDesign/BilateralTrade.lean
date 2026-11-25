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

-- At reports `(1/4, 3/4)` an efficient, DSIC, IR mechanism charges the buyer
-- `1/4` and pays the seller `3/4`: the deficit that weak budget balance forbids.
example (M : BilateralMechanism) (hE : Efficient M) (hB : BuyerDSIC M)
    (hS : SellerDSIC M) (hIR : ExPostIR M) :
    M.payBuyer (1 / 4) (3 / 4) = 1 / 4 ∧ M.paySeller (1 / 4) (3 / 4) = 3 / 4 := by
  have hs : (1 / 4 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
  have hb : (3 / 4 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
  exact ⟨payBuyer_eq_of_lt M hE hB hIR hs hb (by norm_num) (by norm_num),
    paySeller_eq_of_lt M hE hS hIR hs hb (by norm_num) (by norm_num)⟩

-- The posted-price mechanism at `1/2` passes every requirement but efficiency.
example : BuyerDSIC (postedPrice (1 / 2 : ℝ)) ∧ SellerDSIC (postedPrice (1 / 2 : ℝ)) ∧
    ExPostIR (postedPrice (1 / 2 : ℝ)) ∧ WeaklyBudgetBalanced (postedPrice (1 / 2 : ℝ)) ∧
    ¬ Efficient (postedPrice (1 / 2 : ℝ)) := by
  have hp : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
  exact ⟨postedPrice_buyerDSIC, postedPrice_sellerDSIC, postedPrice_exPostIR,
    postedPrice_weaklyBudgetBalanced, postedPrice_not_efficient hp⟩

-- Posted-price allocation at `1/2`: trade at `(0, 1)`, no trade at `(3/4, 1)`
-- although `3/4 < 1`, and no trade at `(0, 1/4)` although `0 < 1/4`.
example : (postedPrice (1 / 2 : ℝ)).alloc 0 1 = 1 := by norm_num [postedPrice]

example : (postedPrice (1 / 2 : ℝ)).alloc (3 / 4) 1 = 0 := by norm_num [postedPrice]

example : (postedPrice (1 / 2 : ℝ)).alloc 0 (1 / 4) = 0 := by norm_num [postedPrice]

example (s b : ℝ) : (postedPrice (1 / 2 : ℝ)).payBuyer s b = 1 / 2 ∧
    (postedPrice (1 / 2 : ℝ)).paySeller s b = 1 / 2 :=
  ⟨rfl, rfl⟩

-- Efficiency is tie-neutral: the mechanism trading exactly when `s ≤ b`
-- (ties included) is efficient, which the old `alloc s b = 1 ↔ s < b`
-- formulation would have rejected.
noncomputable def tradeOnTie : BilateralMechanism where
  alloc s b := if s ≤ b then 1 else 0
  payBuyer _ _ := 0
  paySeller _ _ := 0
  alloc_mem s b := by by_cases h : s ≤ b <;> simp [h]

example : Efficient tradeOnTie := by
  intro s _ b _
  constructor
  · intro h
    simp [tradeOnTie, le_of_lt h]
  · intro h
    simp [tradeOnTie, not_le_of_gt h]

example : tradeOnTie.alloc (1 / 2) (1 / 2) = 1 := by norm_num [tradeOnTie]
