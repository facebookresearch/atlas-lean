/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.MechanismDesign.BilateralTrade
import MathlibExt.GameTheory.MechanismDesign.SingleParameter
import Mathlib.Tactic.Linarith

@[expose] public section

/-! # Bilateral trade with probabilities and net transfers

At each pair of reports the outcome consists of a trade probability and two net transfers.
Only the value of the good is weighted by the probability: the transfers already include any
expectation over the mechanism's own randomness. Incentives and participation are checked at
fixed reports, not after each realised coin toss or averaged over the other agent's type.

Under efficiency, charging the buyer `s * x` makes truth optimal against seller report `s`;
paying the seller `b * x` does the same against buyer report `b`. Single-parameter revenue
equivalence then determines each actual transfer up to that agent's utility at the tie. These
two constants need not be zero. Participation alone gives their signs, which force a deficit
whenever `s < b`.

## Reference

* K. Goldner, *DS 574 Algorithmic Mechanism Design*, Lecture 15 (Fall 2025), p. 1,
  Definition 2 and the following utilities and budget condition; p. 2, Theorem 1 on the
  incompatibility of first-best trade with DSIC, ex-post IR and weak budget balance.
  The lecture uses prices conditional on trade and zero utility without trade. The interval
  argument here allows fractional trade at ties and unrestricted net transfers.
  <https://www.kiragoldner.com/teaching/DS574/fall25/L15.pdf>
-/

namespace MathlibExt.GameTheory.MechanismDesign.BilateralTrade

open Set

local notation "I" => Icc (0 : ℝ) 1

/-- A direct mechanism for one seller and one buyer with reports `(s, b)` in `[0,1]²`.
It specifies the probability `x` of trade, the net amount the buyer pays and the net amount
the seller receives. Each amount is real (a negative amount reverses that flow) and is not a
price conditional on trade. As with `BilateralMechanism`, functions are written on real
arguments, but only their restrictions to the unit square describe outcomes. -/
structure ProbabilityMechanism where
  /-- Probability of trading the item at seller report `s` and buyer report `b` in `[0,1]`. -/
  tradeProb : ℝ → ℝ → ℝ
  /-- Net charge to the buyer at reports `(s, b)`; negative means the buyer receives money. -/
  buyerPayment : ℝ → ℝ → ℝ
  /-- Net receipt of the seller at reports `(s, b)`; negative means the seller pays money. -/
  sellerReceipt : ℝ → ℝ → ℝ
  /-- The trade probability belongs to `[0,1]` at every pair of admissible reports. -/
  tradeProb_mem : ∀ s ∈ I, ∀ b ∈ I, tradeProb s b ∈ I

/-- View a deterministic bilateral mechanism with conditional prices as one with a trade
probability and net transfers on `[0,1]²`: retain its binary `alloc`, charge the buyer
`alloc * payBuyer` and pay the seller `alloc * paySeller`. Thus neither pays nor receives
anything without trade, regardless of the quoted prices there. -/
def BilateralMechanism.toProbabilityMechanism (M : BilateralMechanism) : ProbabilityMechanism where
  tradeProb := M.alloc
  buyerPayment s b := M.alloc s b * M.payBuyer s b
  sellerReceipt s b := M.alloc s b * M.paySeller s b
  tradeProb_mem s _ b _ := by rcases M.alloc_mem s b with h | h <;> simp [h]

namespace ProbabilityMechanism

/-- Utility `v * x(s,r) - pB(s,r)` for a buyer of value `v` reporting `r` against seller
report `s` in `[0,1]`. The buyer pays the net transfer `pB` (receives money if negative). -/
def buyerUtility (M : ProbabilityMechanism) (s v r : ℝ) : ℝ :=
  v * M.tradeProb s r - M.buyerPayment s r

/-- Utility `pS(r,b) - c * x(r,b)` for a seller of cost `c` reporting `r` against buyer
report `b` in `[0,1]`. The seller receives the net transfer `pS` (pays money if negative). -/
def sellerUtility (M : ProbabilityMechanism) (c b r : ℝ) : ℝ :=
  M.sellerReceipt r b - c * M.tradeProb r b

/-- Buyer dominant-strategy IC: for every seller report `s`, buyer value `v` and alternative
report `r` in `[0,1]`, reporting `v` maximizes `v * x(s,r) - pB(s,r)`, net of the buyer's
payment. -/
def BuyerDSIC (M : ProbabilityMechanism) : Prop :=
  ∀ s ∈ I, ∀ v ∈ I, ∀ r ∈ I, M.buyerUtility s v r ≤ M.buyerUtility s v v

/-- Seller dominant-strategy IC: for every buyer report `b`, seller cost `c` and alternative
report `r` in `[0,1]`, reporting `c` maximizes `pS(r,b) - c * x(r,b)`, the seller's net
receipt less expected cost. -/
def SellerDSIC (M : ProbabilityMechanism) : Prop :=
  ∀ b ∈ I, ∀ c ∈ I, ∀ r ∈ I, M.sellerUtility c b r ≤ M.sellerUtility c b c

/-- Ex-post efficiency on the unit square: trade with probability one when `s < b` and zero
when `b < s`. Every probability in `[0,1]` is permitted at a tie, where the gain is zero. -/
def Efficient (M : ProbabilityMechanism) : Prop :=
  ∀ s ∈ I, ∀ b ∈ I, (s < b → M.tradeProb s b = 1) ∧ (b < s → M.tradeProb s b = 0)

/-- Ex-post participation with outside utilities zero: at every truthful `(s,b)` in `[0,1]²`,
both `b * x - pB` for the buyer and `pS - s * x` for the seller are nonnegative. -/
def ExPostIR (M : ProbabilityMechanism) : Prop :=
  ∀ s ∈ I, ∀ b ∈ I, 0 ≤ M.buyerUtility s b b ∧ 0 ≤ M.sellerUtility s b s

/-- Pointwise weak budget balance: the net payment made by the buyer covers the net receipt
of the seller, `pS(s,b) ≤ pB(s,b)`, at every `(s,b)` in `[0,1]²`, even without trade. -/
def WeaklyBudgetBalanced (M : ProbabilityMechanism) : Prop :=
  ∀ s ∈ I, ∀ b ∈ I, M.sellerReceipt s b ≤ M.buyerPayment s b

variable {M : ProbabilityMechanism} {s b : ℝ}

/-- At each unit-square profile `(s,b)` an efficient trade probability maximizes the gain
`(b - s) * q` over all probabilities `q ∈ [0,1]`, including at `s = b`. -/
theorem Efficient.gain_le (hE : M.Efficient) (hs : s ∈ I) (hb : b ∈ I) {q : ℝ} (hq : q ∈ I) :
    (b - s) * q ≤ (b - s) * M.tradeProb s b := by
  rcases lt_trichotomy s b with h | rfl | h
  · rw [(hE s hs b hb).1 h]
    exact mul_le_mul_of_nonneg_left hq.2 (sub_nonneg.mpr h.le)
  · simp
  · rw [(hE s hs b hb).2 h]
    exact mul_le_mul_of_nonpos_left hq.1 (sub_nonpos.mpr h.le)

/-- If `(b - s) * x(s,b) = 0` at a profile in `[0,1]²`, ex-post IR and pointwise weak
budget balance force the buyer's payment and seller's receipt to equal `s * x(s,b)`.
Thus both are zero without trade, and both are `t * x(t,t)` at a tie `s = b = t`; the
latter conclusion does not require the tie probability to be zero or one. -/
theorem transfers_of_zero_gain (hir : M.ExPostIR) (hbb : M.WeaklyBudgetBalanced)
    (hs : s ∈ I) (hb : b ∈ I) (hz : (b - s) * M.tradeProb s b = 0) :
    M.buyerPayment s b = s * M.tradeProb s b ∧ M.sellerReceipt s b = s * M.tradeProb s b := by
  obtain ⟨hB, hS⟩ := hir s hs b hb
  unfold buyerUtility at hB
  unfold sellerUtility at hS
  constructor <;> linarith [hbb s hs b hb]

open SingleParameter

-- For IC payments for a common allocation, the integral term is identical. Subtract the
-- formulas at two points, so no choice of the additive constant is imposed.
private theorem payment_increment {Q P P' : ℝ → ℝ} (h : IsIncentiveCompatibleOn Q P 0 1)
    (h' : IsIncentiveCompatibleOn Q P' 0 1) {u v : ℝ} (hu : u ∈ I) (hv : v ∈ I) :
    P v - P u = P' v - P' u := by
  linarith only [h.payment_formula hv, h.payment_formula hu, h'.payment_formula hv,
    h'.payment_formula hu]

/-- Under efficiency and buyer DSIC, the buyer's net payment at any `(s,b)` in `[0,1]²`
is `s * x(s,b)` minus the buyer's truthful utility at `(s,s)`. This includes endpoints
and ties, and requires neither a zero payment without trade nor participation. -/
theorem buyerPayment_eq_threshold_sub_utility (hE : M.Efficient) (hB : M.BuyerDSIC)
    (hs : s ∈ I) (hb : b ∈ I) :
    M.buyerPayment s b = s * M.tradeProb s b - M.buyerUtility s s s := by
  have h : IsIncentiveCompatibleOn (M.tradeProb s) (M.buyerPayment s) 0 1 :=
    fun r hr v hv => hB s hs v hv r hr
  have h' : IsIncentiveCompatibleOn (M.tradeProb s) (fun r => s * M.tradeProb s r) 0 1 := by
    intro r hr v hv
    simpa only [truthfulUtility, ← sub_mul] using hE.gain_le hs hv (M.tradeProb_mem s hs r hr)
  unfold buyerUtility
  linarith only [payment_increment h h' hs hb]

/-- Under efficiency and seller DSIC, the seller's net receipt at any `(s,b)` in `[0,1]²`
is `b * x(s,b)` plus the seller's truthful utility at `(b,b)`. This includes endpoints
and ties, and requires neither a zero receipt without trade nor participation. -/
theorem sellerReceipt_eq_threshold_add_utility (hE : M.Efficient) (hS : M.SellerDSIC)
    (hs : s ∈ I) (hb : b ∈ I) :
    M.sellerReceipt s b = b * M.tradeProb s b + M.sellerUtility b b b := by
  -- Encode the seller's cost as the type, so both the allocation and the payment of
  -- the associated single-parameter agent carry a minus sign.
  let Q r := -M.tradeProb r b
  let P r := -M.sellerReceipt r b
  have h : IsIncentiveCompatibleOn Q P 0 1 := by
    intro r hr c hc
    have hdev := hS b hb c hc r hr
    unfold sellerUtility at hdev
    dsimp [Q, P, truthfulUtility]
    linarith only [hdev]
  have h' : IsIncentiveCompatibleOn Q (fun r => b * Q r) 0 1 := by
    intro r hr c hc
    dsimp [Q, truthfulUtility]
    linarith only [hE.gain_le hc hb (M.tradeProb_mem r hr b hb)]
  have heq := payment_increment h h' hb hs
  dsimp [Q, P] at heq
  unfold sellerUtility
  linarith only [heq]

/-- With efficiency, buyer and seller DSIC and ex-post IR on `[0,1]²`, at every strict
trade `s < b` the buyer pays at most `s` and the seller receives at least `b`. The bounds
hold also at `s = 0` or `b = 1`; they need no budget-balance hypothesis. -/
theorem threshold_bounds (hE : M.Efficient) (hB : M.BuyerDSIC) (hS : M.SellerDSIC)
    (hir : M.ExPostIR) (hs : s ∈ I) (hb : b ∈ I) (hlt : s < b) :
    M.buyerPayment s b ≤ s ∧ b ≤ M.sellerReceipt s b := by
  rw [buyerPayment_eq_threshold_sub_utility hE hB hs hb,
    sellerReceipt_eq_threshold_add_utility hE hS hs hb, (hE s hs b hb).1 hlt, mul_one, mul_one]
  exact ⟨sub_le_self _ (hir s hs s hs).1, le_add_of_nonneg_right (hir b hb b hb).2⟩

/-- No direct bilateral mechanism on `[0,1]²` with trade probability `x` and real net transfers
`pB` paid by the buyer and `pS` received by the seller can satisfy all of: efficiency (`x = 1`
for `s < b`, `x = 0` for `b < s`, unrestricted ties in `[0,1]`); truthful reporting by both
sides against every opposing report for utilities `v * x - pB` and `pS - c * x`; nonnegative
truthful utilities for both at every profile; and pointwise `pS ≤ pB`. Indeed for `s < b`,
two-sided incentives and participation under efficiency force `pB ≤ s < b ≤ pS`. -/
theorem not_exists_efficient_dsic_ir_wbb :
    ¬ ∃ M : ProbabilityMechanism, M.Efficient ∧ M.BuyerDSIC ∧ M.SellerDSIC ∧ M.ExPostIR ∧
      M.WeaklyBudgetBalanced := by
  rintro ⟨M, hE, hB, hS, hir, hbb⟩
  have h₀ : (0 : ℝ) ∈ I := ⟨le_rfl, zero_le_one⟩
  have h₁ : (1 : ℝ) ∈ I := ⟨zero_le_one, le_rfl⟩
  obtain ⟨hp, hr⟩ := threshold_bounds hE hB hS hir h₀ h₁ zero_lt_one
  exact (not_le_of_gt (zero_lt_one : (0 : ℝ) < 1)) (hr.trans ((hbb 0 h₀ 1 h₁).trans hp))

end ProbabilityMechanism

end MathlibExt.GameTheory.MechanismDesign.BilateralTrade
