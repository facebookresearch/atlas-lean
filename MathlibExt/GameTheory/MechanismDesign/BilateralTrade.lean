/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Linarith

@[expose] public section

/-! # Bilateral trade: the dominant-strategy impossibility

One seller owns an item and has cost `s ∈ [0, 1]` for parting with it; one buyer
has value `b ∈ [0, 1]` for it. A deterministic mechanism chooses whether trade
occurs and two prices: what the buyer pays and what the seller receives. This
file proves the dominant-strategy form of the Myerson--Satterthwaite theorem:
no mechanism is simultaneously ex-post efficient (trade iff `b > s`),
dominant-strategy incentive compatible for both sides, ex-post individually
rational, and weakly budget-balanced. The reason is the threshold-payment
argument of Myerson's lemma in this two-agent setting: efficiency, DSIC and IR
force the buyer to pay `s` and the seller to receive `b` whenever trade occurs,
leaving a deficit of `b - s > 0`. The posted-price mechanism is the positive
control: it is DSIC, ex-post IR and weakly budget-balanced, but never efficient.

## References

* R. B. Myerson and M. A. Satterthwaite, "Efficient mechanisms for bilateral
  trading", *J. Econom. Theory* 29(2) (1983), 265--281.
* K. Goldner, DS 574 Algorithmic Mechanism Design, Lecture 15 (Fall 2025),
  Theorem 1 and conditions (1)--(3): the dominant-strategy statement formalized
  here. The original Bayesian form of Myerson--Satterthwaite is not treated.
-/

namespace MathlibExt.GameTheory.MechanismDesign.BilateralTrade

/-- A deterministic bilateral-trade mechanism on reports: `alloc s b ∈ {0, 1}` is the
trade decision when the seller reports cost `s` and the buyer reports value `b`,
`payBuyer s b` is the price charged to the buyer and `paySeller s b` the amount paid
to the seller when trade occurs. -/
structure BilateralMechanism where
  alloc : ℝ → ℝ → ℝ
  payBuyer : ℝ → ℝ → ℝ
  paySeller : ℝ → ℝ → ℝ
  alloc_mem : ∀ s b, alloc s b = 0 ∨ alloc s b = 1

/-- Buyer utility with true value `v` when the seller reports `s` and the buyer
reports `r`: `x * (v - pB)`, and `0` when there is no trade. -/
def buyerUtil (M : BilateralMechanism) (s v r : ℝ) : ℝ :=
  M.alloc s r * (v - M.payBuyer s r)

/-- Seller utility with true cost `c` when the buyer reports `b` and the seller
reports `r`: `x * (pS - c)`, and `0` when there is no trade. -/
def sellerUtil (M : BilateralMechanism) (c b r : ℝ) : ℝ :=
  M.alloc r b * (M.paySeller r b - c)

/-- Dominant-strategy incentive compatibility for the buyer, for types and reports
in `[0, 1]`: against every seller report, truthful reporting maximizes buyer utility. -/
def BuyerDSIC (M : BilateralMechanism) : Prop :=
  ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ v ∈ Set.Icc (0 : ℝ) 1, ∀ r ∈ Set.Icc (0 : ℝ) 1,
    buyerUtil M s v r ≤ buyerUtil M s v v

/-- Dominant-strategy incentive compatibility for the seller, for types and reports
in `[0, 1]`: against every buyer report, truthful reporting maximizes seller utility. -/
def SellerDSIC (M : BilateralMechanism) : Prop :=
  ∀ b ∈ Set.Icc (0 : ℝ) 1, ∀ c ∈ Set.Icc (0 : ℝ) 1, ∀ r ∈ Set.Icc (0 : ℝ) 1,
    sellerUtil M c b r ≤ sellerUtil M c b c

/-- Ex-post efficiency for reports in `[0, 1]`: trade occurs if and only if the
reported buyer value exceeds the reported seller cost. -/
def Efficient (M : BilateralMechanism) : Prop :=
  ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ Set.Icc (0 : ℝ) 1, M.alloc s b = 1 ↔ s < b

/-- Ex-post individual rationality for types in `[0, 1]`: truthful participation
gives both sides nonnegative utility at every report profile. -/
def ExPostIR (M : BilateralMechanism) : Prop :=
  ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ Set.Icc (0 : ℝ) 1,
    0 ≤ buyerUtil M s b b ∧ 0 ≤ sellerUtil M s b s

/-- Weak budget balance: whenever trade occurs, the buyer's payment covers the
seller's receipt. -/
def WeaklyBudgetBalanced (M : BilateralMechanism) : Prop :=
  ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ Set.Icc (0 : ℝ) 1,
    M.alloc s b = 1 → M.paySeller s b ≤ M.payBuyer s b

/-- **Threshold price for the buyer.** In an efficient, buyer-DSIC, ex-post IR
mechanism, whenever trade occurs at reports `(s, b)` with `s < b`, the buyer pays
exactly `s`. -/
theorem payBuyer_eq_of_lt (M : BilateralMechanism) (hE : Efficient M)
    (hD : BuyerDSIC M) (hIR : ExPostIR M) {s b : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) (h : s < b) :
    M.payBuyer s b = s := by
  have hZero : ∀ s b : ℝ, s ∈ Set.Icc (0:ℝ) 1 → b ∈ Set.Icc (0:ℝ) 1 →
      ¬ s < b → M.alloc s b = 0 := by
    intro s b hs hb hnb
    rcases M.alloc_mem s b with h0 | h1
    · exact h0
    · exfalso
      have hlt := (hE s hs b hb).mp h1
      exact hnb hlt
  have hConst : ∀ r : ℝ, r ∈ Set.Icc (0:ℝ) 1 → s < r →
      M.payBuyer s r = M.payBuyer s b := by
    intro r hr hsr
    have hr1 : M.alloc s r = 1 := (hE s hs r hr).mpr hsr
    have hb1 : M.alloc s b = 1 := (hE s hs b hb).mpr h
    have d1 := hD s hs b hb r hr
    have d2 := hD s hs r hr b hb
    simp only [buyerUtil, hr1, hb1, one_mul] at d1 d2
    linarith
  have hLower : s ≤ M.payBuyer s b := by
    have hss0 : M.alloc s s = 0 := hZero s s hs hs (lt_irrefl s)
    have hb1 : M.alloc s b = 1 := (hE s hs b hb).mpr h
    have d0 := hD s hs s hs b hb
    simp only [buyerUtil, hss0, hb1, zero_mul, one_mul] at d0
    linarith
  have hUpper : M.payBuyer s b ≤ s := by
    by_contra hcon
    have hlt : s < M.payBuyer s b := not_le.mp hcon
    have hmin : s < min b (M.payBuyer s b) := lt_min h hlt
    obtain ⟨r, hsr, hrmin⟩ := exists_between hmin
    have hrb : r < b := lt_of_lt_of_le hrmin (min_le_left _ _)
    have hrpay : r < M.payBuyer s b := lt_of_lt_of_le hrmin (min_le_right _ _)
    obtain ⟨hs0, _⟩ := Set.mem_Icc.mp hs
    obtain ⟨_, hb1le⟩ := Set.mem_Icc.mp hb
    have hr0 : (0:ℝ) ≤ r := by linarith
    have hr1le : r ≤ 1 := by linarith
    have hr : r ∈ Set.Icc (0:ℝ) 1 := Set.mem_Icc.mpr ⟨hr0, hr1le⟩
    have hconst := hConst r hr hsr
    have hr1alloc : M.alloc s r = 1 := (hE s hs r hr).mpr hsr
    have hir := (hIR s hs r hr).1
    simp only [buyerUtil, hr1alloc, one_mul] at hir
    rw [hconst] at hir
    linarith
  exact le_antisymm hUpper hLower

/-- **Threshold receipt for the seller.** In an efficient, seller-DSIC, ex-post IR
mechanism, whenever trade occurs at reports `(s, b)` with `s < b`, the seller
receives exactly `b`. -/
theorem paySeller_eq_of_lt (M : BilateralMechanism) (hE : Efficient M)
    (hD : SellerDSIC M) (hIR : ExPostIR M) {s b : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) (h : s < b) :
    M.paySeller s b = b := by
  have hZero : ∀ s b : ℝ, s ∈ Set.Icc (0:ℝ) 1 → b ∈ Set.Icc (0:ℝ) 1 →
      ¬ s < b → M.alloc s b = 0 := by
    intro s b hs hb hnb
    rcases M.alloc_mem s b with h0 | h1
    · exact h0
    · exfalso
      have hlt := (hE s hs b hb).mp h1
      exact hnb hlt
  have hConst : ∀ c : ℝ, c ∈ Set.Icc (0:ℝ) 1 → c < b →
      M.paySeller c b = M.paySeller s b := by
    intro c hc hcb
    have hc1 : M.alloc c b = 1 := (hE c hc b hb).mpr hcb
    have hs1 : M.alloc s b = 1 := (hE s hs b hb).mpr h
    have d1 := hD b hb s hs c hc
    have d2 := hD b hb c hc s hs
    simp only [sellerUtil, hc1, hs1, one_mul] at d1 d2
    linarith
  have hUpper : M.paySeller s b ≤ b := by
    have hbb0 : M.alloc b b = 0 := hZero b b hb hb (lt_irrefl b)
    have hsb1 : M.alloc s b = 1 := (hE s hs b hb).mpr h
    have d0 := hD b hb b hb s hs
    simp only [sellerUtil, hbb0, hsb1, zero_mul, one_mul] at d0
    linarith
  have hLower : b ≤ M.paySeller s b := by
    by_contra hcon
    have hlt : M.paySeller s b < b := not_le.mp hcon
    have hmax : max s (M.paySeller s b) < b := max_lt h hlt
    obtain ⟨c, hcmax, hcb⟩ := exists_between hmax
    have hpayc : M.paySeller s b < c :=
      lt_of_le_of_lt (le_max_right _ _) hcmax
    obtain ⟨hs0, _⟩ := Set.mem_Icc.mp hs
    obtain ⟨_, hb1le⟩ := Set.mem_Icc.mp hb
    have hc0 : (0:ℝ) ≤ c := by
      have hsc : s < c := lt_of_le_of_lt (le_max_left _ _) hcmax
      linarith
    have hc1le : c ≤ 1 := by linarith
    have hc : c ∈ Set.Icc (0:ℝ) 1 := Set.mem_Icc.mpr ⟨hc0, hc1le⟩
    have hconst := hConst c hc hcb
    have hc1alloc : M.alloc c b = 1 := (hE c hc b hb).mpr hcb
    have hir := (hIR c hc b hb).2
    simp only [sellerUtil, hc1alloc, one_mul] at hir
    rw [hconst] at hir
    linarith
  exact le_antisymm hUpper hLower

/-- **Dominant-strategy bilateral-trade impossibility** (Myerson–Satterthwaite,
dominant-strategy form). No bilateral-trade mechanism on `[0, 1]` types is
simultaneously ex-post efficient, DSIC for both sides, ex-post individually
rational, and weakly budget-balanced: efficiency forces the buyer to pay `s` and
the seller to receive `b` on trade, a deficit of `b - s > 0`. -/
theorem not_exists_efficient_dsic_ir_wbb :
    ¬ ∃ M : BilateralMechanism, Efficient M ∧ BuyerDSIC M ∧ SellerDSIC M ∧
      ExPostIR M ∧ WeaklyBudgetBalanced M := by
  intro hex
  obtain ⟨M, hE, hBD, hSD, hIR, hWBB⟩ := hex
  have hs : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := Set.mem_Icc.mpr ⟨le_refl 0, zero_le_one⟩
  have hb : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := Set.mem_Icc.mpr ⟨zero_le_one, le_refl 1⟩
  have h01 : (0:ℝ) < 1 := zero_lt_one
  have hPayB := payBuyer_eq_of_lt M hE hBD hIR hs hb h01
  have hPayS := paySeller_eq_of_lt M hE hSD hIR hs hb h01
  have hall : M.alloc 0 1 = 1 := (hE 0 hs 1 hb).mpr h01
  have hle := hWBB 0 hs 1 hb hall
  rw [hPayB, hPayS] at hle
  linarith

/-- The posted-price mechanism at price `p`: trade occurs if and only if the
reported seller cost is at most `p` and the reported buyer value is at least `p`;
both sides transact at `p`. -/
noncomputable def postedPrice (p : ℝ) : BilateralMechanism where
  alloc s b := if s ≤ p ∧ p ≤ b then 1 else 0
  payBuyer _ _ := p
  paySeller _ _ := p
  alloc_mem s b := by
    by_cases h : s ≤ p ∧ p ≤ b <;> simp [h]

/-- The posted-price mechanism is DSIC for the buyer. -/
theorem postedPrice_buyerDSIC {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    BuyerDSIC (postedPrice p) := by
  intro s hs v hv r hr
  simp only [buyerUtil, postedPrice]
  by_cases hsp : s ≤ p
  · by_cases hpv : p ≤ v
    · by_cases hpr : p ≤ r
      · simp [hsp, hpv, hpr]
      · simp [hsp, hpv, hpr]
    · by_cases hpr : p ≤ r
      · simp only [hsp, hpv, hpr, and_true, and_false, ite_true, ite_false,
          zero_mul, one_mul]
        have hvp : v < p := not_le.mp hpv
        linarith
      · simp [hsp, hpv, hpr]
  · simp [hsp]

/-- The posted-price mechanism is DSIC for the seller. -/
theorem postedPrice_sellerDSIC {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    SellerDSIC (postedPrice p) := by
  intro b hb c hc r hr
  simp only [sellerUtil, postedPrice]
  by_cases hpb : p ≤ b
  · by_cases hcp : c ≤ p
    · by_cases hrp : r ≤ p
      · simp [hpb, hcp, hrp]
      · simp [hpb, hcp, hrp]
    · by_cases hrp : r ≤ p
      · simp only [hpb, hcp, hrp, and_true, ite_true, ite_false, zero_mul,
          one_mul]
        have hpc : p < c := not_le.mp hcp
        linarith
      · simp [hpb, hcp, hrp]
  · simp [hpb]

/-- The posted-price mechanism is ex-post individually rational. -/
theorem postedPrice_exPostIR {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    ExPostIR (postedPrice p) := by
  intro s hs b hb
  simp only [buyerUtil, sellerUtil, postedPrice]
  by_cases h : s ≤ p ∧ p ≤ b
  · obtain ⟨hsp, hpb⟩ := h
    simp [hsp, hpb]
  · simp [h]

/-- The posted-price mechanism is weakly budget-balanced (both sides use `p`). -/
theorem postedPrice_weaklyBudgetBalanced {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    WeaklyBudgetBalanced (postedPrice p) := by
  intro s hs b hb hall
  simp only [postedPrice]
  exact le_refl p

/-- No posted-price mechanism with price in `[0, 1]` is ex-post efficient:
some gains from trade are always left unrealized. -/
theorem postedPrice_not_efficient {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    ¬ Efficient (postedPrice p) := by
  intro hE
  obtain ⟨hp0, hp1⟩ := Set.mem_Icc.mp hp
  by_cases hlt : p < 1
  · have hs0 : (0:ℝ) ≤ (p + 1) / 2 := by linarith
    have hs1 : (p + 1) / 2 ≤ 1 := by linarith
    have hs : (p + 1) / 2 ∈ Set.Icc (0:ℝ) 1 := Set.mem_Icc.mpr ⟨hs0, hs1⟩
    have hb : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := Set.mem_Icc.mpr ⟨zero_le_one, le_refl 1⟩
    have hsb : (p + 1) / 2 < 1 := by linarith
    have hiff := hE _ hs _ hb
    simp only [postedPrice] at hiff
    have hnle : ¬ (p + 1) / 2 ≤ p := by linarith
    have hcond : ¬ ((p + 1) / 2 ≤ p ∧ p ≤ (1:ℝ)) := fun h => hnle h.1
    rw [ite_eq_right hcond] at hiff
    exact zero_ne_one (hiff.mpr hsb)
  · have hp_eq : p = 1 := by
      have hge : 1 ≤ p := not_lt.mp hlt
      linarith
    have hs : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := Set.mem_Icc.mpr ⟨le_refl 0, zero_le_one⟩
    have hb : (1:ℝ)/2 ∈ Set.Icc (0:ℝ) 1 := Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
    have hsb : (0:ℝ) < 1/2 := by linarith
    have hiff := hE _ hs _ hb
    simp only [postedPrice] at hiff
    rw [hp_eq] at hiff
    have hcond : ¬ ((0:ℝ) ≤ 1 ∧ (1:ℝ) ≤ 1/2) := by
      intro h
      obtain ⟨_, h2⟩ := h
      linarith
    rw [ite_eq_right hcond] at hiff
    exact zero_ne_one (hiff.mpr hsb)

end MathlibExt.GameTheory.MechanismDesign.BilateralTrade
