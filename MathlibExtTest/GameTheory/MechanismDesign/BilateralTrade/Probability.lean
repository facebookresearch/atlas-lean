/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.MechanismDesign.BilateralTrade.Probability
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open MathlibExt.GameTheory.MechanismDesign.BilateralTrade

local notation "I" => Set.Icc (0 : ℝ) 1

-- Conditional prices convert to net transfers, preserving even misreport utilities.
example (M : BilateralMechanism) (s b r : ℝ) :
    M.toProbabilityMechanism.buyerUtility s b r = buyerUtil M s b r ∧
    M.toProbabilityMechanism.sellerUtility s b r = sellerUtil M s b r := by
  constructor <;> simp only [ProbabilityMechanism.buyerUtility, ProbabilityMechanism.sellerUtility,
    BilateralMechanism.toProbabilityMechanism, buyerUtil, sellerUtil, mul_sub, mul_comm]

example (M : BilateralMechanism) :
    M.toProbabilityMechanism.WeaklyBudgetBalanced ↔ WeaklyBudgetBalanced M := by
  constructor
  · intro h s hs b hb h₁
    simpa [BilateralMechanism.toProbabilityMechanism, h₁] using h s hs b hb
  · intro h s hs b hb
    rcases M.alloc_mem s b with h₀ | h₁
    · simp [BilateralMechanism.toProbabilityMechanism, h₀]
    · simpa [BilateralMechanism.toProbabilityMechanism, h₁] using h s hs b hb h₁

private noncomputable def halfTie (s b : ℝ) : ℝ :=
  if s < b then 1 else if b < s then 0 else 1 / 2

private noncomputable def menu (pB pS : ℝ → ℝ → ℝ) : ProbabilityMechanism where
  tradeProb := halfTie
  buyerPayment := pB
  sellerReceipt := pS
  tradeProb_mem s _ b _ := by unfold halfTie; split_ifs <;> norm_num

private theorem menu_efficient (pB pS : ℝ → ℝ → ℝ) : (menu pB pS).Efficient := by
  intro s _ b _
  exact ⟨fun h => by simp [menu, halfTie, h], fun h => by simp [menu, halfTie, h, h.asymm]⟩

-- Paying the seller's report on trade is efficient, buyer-IC, IR and balanced, but a
-- low-cost seller can gain by bidding higher. The seller's IC clause cannot be dropped.
private noncomputable def costPrice : ProbabilityMechanism :=
  menu (fun s b => s * halfTie s b) (fun s b => s * halfTie s b)

private theorem costPrice_ir : costPrice.ExPostIR := by
  intro s hs b hb
  have he : costPrice.Efficient := menu_efficient _ _
  have hg := he.gain_le hs hb (q := 0) (by simp)
  change 0 ≤ b * halfTie s b - s * halfTie s b ∧ 0 ≤ s * halfTie s b - s * halfTie s b
  change (b - s) * 0 ≤ (b - s) * halfTie s b at hg
  constructor <;> linarith

private theorem costPrice_wbb : costPrice.WeaklyBudgetBalanced := fun _ _ _ _ => le_rfl

example : costPrice.Efficient ∧ costPrice.BuyerDSIC ∧ costPrice.ExPostIR ∧
    costPrice.WeaklyBudgetBalanced ∧ ¬ costPrice.SellerDSIC := by
  have he : costPrice.Efficient := menu_efficient _ _
  refine ⟨he, ?_, costPrice_ir, costPrice_wbb, ?_⟩
  · intro s hs v hv r hr
    simpa only [costPrice, menu, ProbabilityMechanism.buyerUtility, ← sub_mul] using
      he.gain_le hs hv (costPrice.tradeProb_mem s hs r hr)
  · intro h
    have bad := h 1 (by simp) 0 (by simp) (1 / 2) (by norm_num)
    norm_num [ProbabilityMechanism.sellerUtility, costPrice, menu, halfTie] at bad

-- A genuine interior tie: half-trade at cost/value 1/2 gives transfers 1/4 and zero
-- truthful utilities. IR and WBB normalize transfers here, not the probability.
example : costPrice.tradeProb (1 / 2) (1 / 2) = 1 / 2 ∧
    costPrice.buyerPayment (1 / 2) (1 / 2) = 1 / 4 ∧
    costPrice.sellerReceipt (1 / 2) (1 / 2) = 1 / 4 ∧
    costPrice.buyerUtility (1 / 2) (1 / 2) (1 / 2) = 0 ∧
    costPrice.sellerUtility (1 / 2) (1 / 2) (1 / 2) = 0 := by
  norm_num [costPrice, ProbabilityMechanism.buyerUtility, ProbabilityMechanism.sellerUtility,
    menu, halfTie]

-- An efficient two-sided IC, IR mechanism gives each agent an unconditional subsidy of
-- one, so transfers need not vanish without trade. Its strict-trade bounds are not equalities.
private noncomputable def subsidized : ProbabilityMechanism :=
  menu (fun s b => s * halfTie s b - 1) (fun s b => b * halfTie s b + 1)

example : subsidized.Efficient ∧ subsidized.BuyerDSIC ∧ subsidized.SellerDSIC ∧
    subsidized.ExPostIR ∧ ¬ subsidized.WeaklyBudgetBalanced := by
  have he : subsidized.Efficient := menu_efficient _ _
  refine ⟨he, ?_, ?_, ?_, ?_⟩
  · intro s hs v hv r hr
    have hg := he.gain_le hs hv (subsidized.tradeProb_mem s hs r hr)
    dsimp [subsidized, menu, ProbabilityMechanism.buyerUtility] at hg ⊢
    linarith only [hg]
  · intro b hb c hc r hr
    have hg := he.gain_le hc hb (subsidized.tradeProb_mem r hr b hb)
    dsimp [subsidized, menu, ProbabilityMechanism.sellerUtility] at hg ⊢
    linarith only [hg]
  · intro s hs b hb
    have hg := he.gain_le hs hb (q := 0) (by simp)
    dsimp [subsidized, menu, ProbabilityMechanism.buyerUtility,
      ProbabilityMechanism.sellerUtility] at hg ⊢
    constructor <;> linarith only [hg]
  · intro h
    have bad := h 1 (by simp) 0 (by simp)
    norm_num [subsidized, menu, halfTie] at bad

example : subsidized.tradeProb 1 0 = 0 ∧ subsidized.buyerPayment 1 0 = -1 ∧
    subsidized.sellerReceipt 1 0 = 1 ∧ subsidized.buyerUtility 1 0 0 = 1 ∧
    subsidized.sellerUtility 1 0 1 = 1 := by
  norm_num [subsidized, menu, halfTie, ProbabilityMechanism.buyerUtility,
    ProbabilityMechanism.sellerUtility]

example : subsidized.buyerPayment (1 / 4) (3 / 4) < 1 / 4 ∧
    3 / 4 < subsidized.sellerReceipt (1 / 4) (3 / 4) := by
  norm_num [subsidized, menu, halfTie]

-- Weak balance really is an inequality. With the buyer paying its own value and the seller
-- receiving its own cost on trade, the platform keeps all the gains, strictly so at (0,1).
example : ∃ M : ProbabilityMechanism, M.Efficient ∧ M.ExPostIR ∧ M.WeaklyBudgetBalanced ∧
    M.sellerReceipt 0 1 < M.buyerPayment 0 1 := by
  let M := menu (fun s b => b * halfTie s b) (fun s b => s * halfTie s b)
  have he : M.Efficient := menu_efficient _ _
  refine ⟨M, he, fun _ _ _ _ => ⟨sub_nonneg.mpr le_rfl, sub_nonneg.mpr le_rfl⟩, ?_, ?_⟩
  · intro s hs b hb
    have hg := he.gain_le hs hb (q := 0) (by simp)
    dsimp [M, menu] at hg ⊢
    linarith only [hg]
  · norm_num [M, menu, halfTie]

example (M : ProbabilityMechanism) (hir : M.ExPostIR) (hbb : M.WeaklyBudgetBalanced)
    {s b : ℝ} (hs : s ∈ I) (hb : b ∈ I) (h₀ : M.tradeProb s b = 0) :
    M.buyerPayment s b = 0 ∧ M.sellerReceipt s b = 0 := by
  simpa [h₀] using ProbabilityMechanism.transfers_of_zero_gain hir hbb hs hb (by simp [h₀])

example (M : ProbabilityMechanism) (hir : M.ExPostIR) (hbb : M.WeaklyBudgetBalanced)
    {t : ℝ} (ht : t ∈ I) :
    M.buyerPayment t t = t * M.tradeProb t t ∧ M.sellerReceipt t t = t * M.tradeProb t t :=
  ProbabilityMechanism.transfers_of_zero_gain hir hbb ht ht (by simp)
