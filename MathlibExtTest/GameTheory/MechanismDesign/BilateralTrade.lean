/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.MechanismDesign.BilateralTrade
import MathlibExt.GameTheory.MechanismDesign.SingleParameter
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

open MathlibExt.GameTheory.MechanismDesign
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

-- Efficiency alone fixes no price: `tradeOnTie` is efficient and charges nothing, but it is
-- not buyer-DSIC (a buyer of value `1/4` facing the seller report `1/2` gains by reporting `1`).
example : ¬ BuyerDSIC tradeOnTie := by
  intro h
  have := h (1 / 2) ⟨by norm_num, by norm_num⟩ (1 / 4) ⟨by norm_num, by norm_num⟩ 1
    ⟨by norm_num, by norm_num⟩
  norm_num [buyerUtil, tradeOnTie] at this

-- The threshold prices are attainable: charging the buyer the seller's report and paying the
-- seller the buyer's report is efficient, DSIC for both sides and ex-post IR, and it runs a
-- deficit: without weak budget balance the other requirements are compatible.
noncomputable def thresholdMechanism : BilateralMechanism where
  alloc s b := if s < b then 1 else 0
  payBuyer s _ := s
  paySeller _ b := b
  alloc_mem s b := by by_cases h : s < b <;> simp [h]

example : Efficient thresholdMechanism ∧ BuyerDSIC thresholdMechanism ∧
    SellerDSIC thresholdMechanism ∧ ExPostIR thresholdMechanism ∧
    ¬ WeaklyBudgetBalanced thresholdMechanism := by
  refine ⟨fun s _ b _ => ⟨fun h => ?_, fun h => ?_⟩, fun s _ v _ r _ => ?_,
    fun b _ c _ r _ => ?_, fun s _ b _ => ?_, fun h => ?_⟩
  · simp [thresholdMechanism, h]
  · simp [thresholdMechanism, not_lt_of_gt h]
  · simp only [buyerUtil, thresholdMechanism]
    by_cases hr : s < r <;> by_cases hv : s < v <;> simp [hr, hv] <;> linarith
  · simp only [sellerUtil, thresholdMechanism]
    by_cases hr : r < b <;> by_cases hc : c < b <;> simp [hr, hc] <;> linarith
  · simp only [buyerUtil, sellerUtil, thresholdMechanism]
    by_cases h : s < b
    · simp [h]; linarith
    · simp [h]
  · have := h (1 / 4) ⟨by norm_num, by norm_num⟩ (3 / 4) ⟨by norm_num, by norm_num⟩
      (by norm_num [thresholdMechanism])
    norm_num [thresholdMechanism] at this

-- `BuyerDSIC` is Myerson's single-parameter condition for each seller report, and `SellerDSIC`
-- is the same condition on `[-1, 0]` once the seller's cost `c` is read as the value `-c`.
example (M : BilateralMechanism) : BuyerDSIC M ↔ ∀ s ∈ Set.Icc (0 : ℝ) 1,
    SingleParameter.IsIncentiveCompatibleOn (M.alloc s)
      (fun r => M.alloc s r * M.payBuyer s r) 0 1 := by
  simp only [BuyerDSIC, SingleParameter.IsIncentiveCompatibleOn,
    SingleParameter.truthfulUtility, buyerUtil]
  constructor
  · intro h s hs r hr v hv
    have := h s hs v hv r hr
    linarith
  · intro h s hs v hv r hr
    have := h s hs r hr v hv
    linarith

example (M : BilateralMechanism) : SellerDSIC M ↔ ∀ b ∈ Set.Icc (0 : ℝ) 1,
    SingleParameter.IsIncentiveCompatibleOn (fun t => M.alloc (-t) b)
      (fun t => -(M.alloc (-t) b * M.paySeller (-t) b)) (-1) 0 := by
  simp only [SellerDSIC, SingleParameter.IsIncentiveCompatibleOn,
    SingleParameter.truthfulUtility, sellerUtil, Set.mem_Icc]
  constructor
  · intro h b hb r hr t ht
    have := h b hb (-t) ⟨by linarith, by linarith⟩ (-r) ⟨by linarith, by linarith⟩
    linarith
  · intro h b hb c hc r hr
    have := h b hb (-r) ⟨by linarith, by linarith⟩ (-c) ⟨by linarith, by linarith⟩
    simp only [neg_neg] at this
    linarith
