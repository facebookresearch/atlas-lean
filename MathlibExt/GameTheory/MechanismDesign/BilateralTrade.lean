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
occurs and two prices: what the buyer pays and what the seller receives. No money
changes hands without trade: both utilities are `0` when there is no trade. For
these mechanisms this file proves the dominant-strategy impossibility of efficient
bilateral trade: no mechanism is simultaneously ex-post efficient (trade whenever
`b > s`, none whenever `b < s`), dominant-strategy incentive compatible for both
sides, ex-post individually rational, and weakly budget-balanced. The reason is the
threshold-payment argument of Myerson's lemma in this two-agent setting: at an
interior profile `0 < s < b < 1`, efficiency, buyer DSIC and ex-post IR force the
buyer to pay `s`, and efficiency, seller DSIC and ex-post IR force the seller to
receive `b`, leaving a deficit of `b - s > 0`. Efficiency alone fixes no price:
trading exactly when `b > s` with both transfers zero is efficient. The
posted-price mechanism is the positive control: it is DSIC, ex-post IR and weakly
budget-balanced, but never efficient.

This is not the Bayesian Myerson--Satterthwaite theorem, nor a statement about
mechanisms that randomize trade or make payments without trade.

## References

* R. B. Myerson and M. A. Satterthwaite, "Efficient mechanisms for bilateral
  trading", *J. Econom. Theory* 29(2) (1983), 265--281.
* K. Goldner, DS 574 Algorithmic Mechanism Design, Lecture 15 (Fall 2025),
  Definition 2, the utilities after it (utility `0` without trade), conditions
  (1)--(3) and Theorem 1: the dominant-strategy statement formalized here. The
  original Bayesian form of Myerson--Satterthwaite is not treated.
-/

namespace MathlibExt.GameTheory.MechanismDesign.BilateralTrade

/-- **Bilateral-trade mechanism.** A deterministic bilateral-trade mechanism on reports:
`alloc s b ∈ {0, 1}` is the trade decision when the seller reports cost `s` and the buyer
reports value `b`, `payBuyer s b` is the price charged to the buyer and `paySeller s b` the
amount paid to the seller when trade occurs. No money changes hands without trade: `buyerUtil`
and `sellerUtil` are `0` when `alloc s b = 0`, whatever the two prices are there. The mechanism
is defined at all real reports; DSIC, efficiency, individual rationality and weak budget balance
constrain it only at reports in `[0, 1]`. -/
structure BilateralMechanism where
  alloc : ℝ → ℝ → ℝ
  payBuyer : ℝ → ℝ → ℝ
  paySeller : ℝ → ℝ → ℝ
  alloc_mem : ∀ s b, alloc s b = 0 ∨ alloc s b = 1

/-- **Buyer utility.** The utility of a buyer with true value `v` when the seller reports `s`
and the buyer reports `r`: `x * (v - pB)`, and `0` when there is no trade. -/
def buyerUtil (M : BilateralMechanism) (s v r : ℝ) : ℝ :=
  M.alloc s r * (v - M.payBuyer s r)

/-- **Seller utility.** The utility of a seller with true cost `c` when the buyer reports `b`
and the seller reports `r`: `x * (pS - c)`, and `0` when there is no trade. -/
def sellerUtil (M : BilateralMechanism) (c b r : ℝ) : ℝ :=
  M.alloc r b * (M.paySeller r b - c)

/-- **Buyer DSIC.** Dominant-strategy incentive compatibility for the buyer, for types and
reports in `[0, 1]`: against every seller report, truthful reporting maximizes buyer utility.
For each seller report `s` this is `SingleParameter.IsIncentiveCompatibleOn` on `[0, 1]` with
allocation `M.alloc s` and payment `fun r => M.alloc s r * M.payBuyer s r`. It is stated per
side, not bundled with `SellerDSIC` as in `IsDominantStrategyIncentiveCompatible`, because each
threshold price uses one side's condition. -/
def BuyerDSIC (M : BilateralMechanism) : Prop :=
  ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ v ∈ Set.Icc (0 : ℝ) 1, ∀ r ∈ Set.Icc (0 : ℝ) 1,
    buyerUtil M s v r ≤ buyerUtil M s v v

/-- **Seller DSIC.** Dominant-strategy incentive compatibility for the seller, for types and
reports in `[0, 1]`: against every buyer report, truthful reporting maximizes seller utility.
For each buyer report `b` this is `SingleParameter.IsIncentiveCompatibleOn` on `[-1, 0]`
once the cost `c` is read as the value `-c`. -/
def SellerDSIC (M : BilateralMechanism) : Prop :=
  ∀ b ∈ Set.Icc (0 : ℝ) 1, ∀ c ∈ Set.Icc (0 : ℝ) 1, ∀ r ∈ Set.Icc (0 : ℝ) 1,
    sellerUtil M c b r ≤ sellerUtil M c b c

/-- **Ex-post efficiency.** For reports in `[0, 1]`, trade is required when the reported buyer
value strictly exceeds the reported seller cost, and forbidden when it is strictly below it.
At equality both outcomes maximize welfare, so the allocation is unconstrained there. -/
def Efficient (M : BilateralMechanism) : Prop :=
  ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ Set.Icc (0 : ℝ) 1,
    (s < b → M.alloc s b = 1) ∧ (b < s → M.alloc s b = 0)

/-- **Ex-post individual rationality.** For types in `[0, 1]`, truthful participation gives
both sides nonnegative utility at every report profile. -/
def ExPostIR (M : BilateralMechanism) : Prop :=
  ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ Set.Icc (0 : ℝ) 1,
    0 ≤ buyerUtil M s b b ∧ 0 ≤ sellerUtil M s b s

/-- **Weak budget balance.** For reports in `[0, 1]`, whenever trade occurs, the buyer's payment
covers the seller's receipt. -/
def WeaklyBudgetBalanced (M : BilateralMechanism) : Prop :=
  ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ Set.Icc (0 : ℝ) 1,
    M.alloc s b = 1 → M.paySeller s b ≤ M.payBuyer s b

/-- **Threshold price for the buyer.** In an efficient, buyer-DSIC, ex-post IR
mechanism, whenever trade occurs at reports `(s, b)` with `0 < s < b ≤ 1`, the buyer
pays exactly `s`. The interior hypothesis `0 < s` is essential: with tie-neutral
efficiency, DSIC and IR do not pin the price at the boundary `s = 0`. -/
theorem payBuyer_eq_of_lt (M : BilateralMechanism) (hE : Efficient M)
    (hD : BuyerDSIC M) (hIR : ExPostIR M) {s b : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (hs0 : 0 < s) (h : s < b) :
    M.payBuyer s b = s := by
  obtain ⟨hs_lo, hs_hi⟩ := Set.mem_Icc.mp hs
  obtain ⟨hb_lo, hb_hi⟩ := Set.mem_Icc.mp hb
  have hconst : ∀ r ∈ Set.Icc (0 : ℝ) 1, s < r → M.payBuyer s r = M.payBuyer s b := by
    intro r hr hsr
    have halloc_r : M.alloc s r = 1 := (hE s hs r hr).1 hsr
    have halloc_b : M.alloc s b = 1 := (hE s hs b hb).1 h
    have h1 := hD s hs b hb r hr
    have h2 := hD s hs r hr b hb
    simp only [buyerUtil, halloc_r, halloc_b, one_mul] at h1 h2
    have hle1 : M.payBuyer s b ≤ M.payBuyer s r := by linarith
    have hle2 : M.payBuyer s r ≤ M.payBuyer s b := by linarith
    exact le_antisymm hle2 hle1
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hmax : max (M.payBuyer s b) 0 < s := max_lt_iff.mpr ⟨hlt, hs0⟩
    obtain ⟨v, hv_lo, hv_hi⟩ := exists_between hmax
    have hpay_lt_v : M.payBuyer s b < v :=
      lt_of_le_of_lt (le_max_left _ _) hv_lo
    have h0v : (0 : ℝ) < v := lt_of_le_of_lt (le_max_right _ _) hv_lo
    have hv_mem : v ∈ Set.Icc (0 : ℝ) 1 :=
      Set.mem_Icc.mpr ⟨le_of_lt h0v, le_trans (le_of_lt hv_hi) hs_hi⟩
    have halloc_sv : M.alloc s v = 0 := (hE s hs v hv_mem).2 hv_hi
    have halloc_sb : M.alloc s b = 1 := (hE s hs b hb).1 h
    have hdsic := hD s hs v hv_mem b hb
    simp only [buyerUtil, halloc_sb, halloc_sv, one_mul, zero_mul] at hdsic
    linarith
  · have hmin : s < min b (M.payBuyer s b) := lt_min_iff.mpr ⟨h, hgt⟩
    obtain ⟨r, hr_lo, hr_hi⟩ := exists_between hmin
    have hr_lt_b : r < b := lt_of_lt_of_le hr_hi (min_le_left _ _)
    have hr_lt_pay : r < M.payBuyer s b := lt_of_lt_of_le hr_hi (min_le_right _ _)
    have hr_mem : r ∈ Set.Icc (0 : ℝ) 1 :=
      Set.mem_Icc.mpr
        ⟨le_trans hs_lo (le_of_lt hr_lo), le_trans (le_of_lt hr_lt_b) hb_hi⟩
    have halloc_sr : M.alloc s r = 1 := (hE s hs r hr_mem).1 hr_lo
    have hir := (hIR s hs r hr_mem).1
    simp only [buyerUtil, halloc_sr, one_mul] at hir
    have hconst_r := hconst r hr_mem hr_lo
    linarith

/-- **Threshold receipt for the seller.** In an efficient, seller-DSIC, ex-post IR
mechanism, whenever trade occurs at reports `(s, b)` with `0 ≤ s < b < 1`, the seller
receives exactly `b`. The interior hypothesis `b < 1` is essential: with tie-neutral
efficiency, DSIC and IR do not pin the receipt at the boundary `b = 1`. -/
theorem paySeller_eq_of_lt (M : BilateralMechanism) (hE : Efficient M)
    (hD : SellerDSIC M) (hIR : ExPostIR M) {s b : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (hb1 : b < 1) (h : s < b) :
    M.paySeller s b = b := by
  obtain ⟨hs_lo, hs_hi⟩ := Set.mem_Icc.mp hs
  obtain ⟨hb_lo, hb_hi⟩ := Set.mem_Icc.mp hb
  have hconst : ∀ c ∈ Set.Icc (0 : ℝ) 1, c < b → M.paySeller c b = M.paySeller s b := by
    intro c hc hcb
    have halloc_cb : M.alloc c b = 1 := (hE c hc b hb).1 hcb
    have halloc_sb : M.alloc s b = 1 := (hE s hs b hb).1 h
    have h1 := hD b hb c hc s hs
    have h2 := hD b hb s hs c hc
    simp only [sellerUtil, halloc_cb, halloc_sb, one_mul] at h1 h2
    have hle1 : M.paySeller s b ≤ M.paySeller c b := by linarith
    have hle2 : M.paySeller c b ≤ M.paySeller s b := by linarith
    exact le_antisymm hle2 hle1
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hmax : max s (M.paySeller s b) < b := max_lt_iff.mpr ⟨h, hlt⟩
    obtain ⟨c, hc_lo, hc_hi⟩ := exists_between hmax
    have hs_lt_c : s < c := lt_of_le_of_lt (le_max_left _ _) hc_lo
    have hpay_lt_c : M.paySeller s b < c :=
      lt_of_le_of_lt (le_max_right _ _) hc_lo
    have hc_mem : c ∈ Set.Icc (0 : ℝ) 1 :=
      Set.mem_Icc.mpr
        ⟨le_trans hs_lo (le_of_lt hs_lt_c), le_trans (le_of_lt hc_hi) hb_hi⟩
    have halloc_cb : M.alloc c b = 1 := (hE c hc_mem b hb).1 hc_hi
    have hir := (hIR c hc_mem b hb).2
    simp only [sellerUtil, halloc_cb, one_mul] at hir
    have hconst_c := hconst c hc_mem hc_hi
    linarith
  · have hmin : b < min (M.paySeller s b) 1 := lt_min_iff.mpr ⟨hgt, hb1⟩
    obtain ⟨c, hc_lo, hc_hi⟩ := exists_between hmin
    have hc_lt_pay : c < M.paySeller s b := lt_of_lt_of_le hc_hi (min_le_left _ _)
    have hc_lt_1 : c < 1 := lt_of_lt_of_le hc_hi (min_le_right _ _)
    have hc_mem : c ∈ Set.Icc (0 : ℝ) 1 :=
      Set.mem_Icc.mpr ⟨le_trans hb_lo (le_of_lt hc_lo), le_of_lt hc_lt_1⟩
    have halloc_cb : M.alloc c b = 0 := (hE c hc_mem b hb).2 hc_lo
    have halloc_sb : M.alloc s b = 1 := (hE s hs b hb).1 h
    have hdsic := hD b hb c hc_mem s hs
    simp only [sellerUtil, halloc_sb, halloc_cb, one_mul, zero_mul] at hdsic
    linarith

/-- **Dominant-strategy bilateral-trade impossibility.** No deterministic bilateral-trade
mechanism on `[0, 1]` types is simultaneously ex-post efficient, DSIC for both sides, ex-post
individually rational, and weakly budget-balanced. At an interior profile `0 < s < b < 1`
efficiency forces trade; efficiency, buyer DSIC and ex-post IR force the buyer to pay `s`
(`payBuyer_eq_of_lt`), and efficiency, seller DSIC and ex-post IR force the seller to receive
`b` (`paySeller_eq_of_lt`). The seller would then receive `b - s > 0` more than the buyer pays,
which weak budget balance forbids.

The mechanism is deterministic (`alloc s b ∈ {0, 1}`) and has zero transfers off trade by
construction: both utilities are `0` when `alloc s b = 0`. So this is neither the Bayesian
Myerson–Satterthwaite impossibility nor a statement about mechanisms that randomize trade or
make payments without trade.

Source: K. Goldner, DS 574 Algorithmic Mechanism Design, Lecture 15 (Fall 2025), Definition 2,
the utilities after it, conditions (1)–(3) and Theorem 1. -/
theorem not_exists_efficient_dsic_ir_wbb :
    ¬ ∃ M : BilateralMechanism, Efficient M ∧ BuyerDSIC M ∧ SellerDSIC M ∧
      ExPostIR M ∧ WeaklyBudgetBalanced M := by
  intro hex
  obtain ⟨M, hE, hDb, hDs, hIR, hWBB⟩ := hex
  have hs : (1 / 4 : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
    Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
  have hb : (3 / 4 : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
    Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
  have hs0 : (0 : ℝ) < 1 / 4 := by norm_num
  have hb1 : (3 / 4 : ℝ) < 1 := by norm_num
  have hlt : (1 / 4 : ℝ) < 3 / 4 := by norm_num
  have hpayB := payBuyer_eq_of_lt M hE hDb hIR hs hb hs0 hlt
  have hpayS := paySeller_eq_of_lt M hE hDs hIR hs hb hb1 hlt
  have halloc : M.alloc (1 / 4) (3 / 4) = 1 := (hE _ hs _ hb).1 hlt
  have hwbb := hWBB _ hs _ hb halloc
  rw [hpayB, hpayS] at hwbb
  linarith

/-- **Posted-price mechanism.** At price `p`, trade occurs if and only if the reported seller
cost is at most `p` and the reported buyer value is at least `p`; both sides transact at `p`. -/
noncomputable def postedPrice (p : ℝ) : BilateralMechanism where
  alloc s b := if s ≤ p ∧ p ≤ b then 1 else 0
  payBuyer _ _ := p
  paySeller _ _ := p
  alloc_mem s b := by
    by_cases h : s ≤ p ∧ p ≤ b <;> simp [h]

/-- **Posted prices are buyer DSIC.** The posted-price mechanism is DSIC for the buyer. -/
theorem postedPrice_buyerDSIC {p : ℝ} :
    BuyerDSIC (postedPrice p) := by
  intro s hs v hv r hr
  simp only [buyerUtil, postedPrice]
  by_cases hs_le : s ≤ p <;> by_cases hr_le : p ≤ r <;> by_cases hv_le : p ≤ v <;>
    simp [hs_le, hr_le, hv_le]; linarith

/-- **Posted prices are seller DSIC.** The posted-price mechanism is DSIC for the seller. -/
theorem postedPrice_sellerDSIC {p : ℝ} :
    SellerDSIC (postedPrice p) := by
  intro b hb c hc r hr
  simp only [sellerUtil, postedPrice]
  by_cases hb_le : p ≤ b <;> by_cases hr_le : r ≤ p <;> by_cases hc_le : c ≤ p <;>
    simp [hb_le, hr_le, hc_le]; linarith

/-- **Posted prices are ex-post individually rational.** The posted-price mechanism is ex-post
individually rational. -/
theorem postedPrice_exPostIR {p : ℝ} :
    ExPostIR (postedPrice p) := by
  intro s hs b hb
  simp only [buyerUtil, sellerUtil, postedPrice]
  by_cases h : s ≤ p ∧ p ≤ b <;> simp [h]

/-- **Posted prices are weakly budget-balanced.** The posted-price mechanism is weakly
budget-balanced (both sides use `p`). -/
theorem postedPrice_weaklyBudgetBalanced {p : ℝ} :
    WeaklyBudgetBalanced (postedPrice p) := by
  intro s hs b hb halloc
  simp [postedPrice]

/-- **Posted prices are not efficient.** No posted-price mechanism with price in `[0, 1]` is
ex-post efficient: some gains from trade are always left unrealized. -/
theorem postedPrice_not_efficient {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    ¬ Efficient (postedPrice p) := by
  obtain ⟨hp0_le, hp1_le⟩ := Set.mem_Icc.mp hp
  by_cases hp0 : p = 0
  · subst hp0
    intro hE
    have hs : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
      Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
    have hb : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
      Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
    have hlt : (1 / 2 : ℝ) < 1 := by norm_num
    have h1 := (hE _ hs _ hb).1 hlt
    simp only [postedPrice] at h1
    norm_num at h1
  · intro hE
    have hne : (0 : ℝ) ≠ p := fun h => hp0 h.symm
    have hpos : (0 : ℝ) < p := lt_of_le_of_ne hp0_le hne
    have hs : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.mem_Icc.mpr ⟨le_refl 0, zero_le_one⟩
    have hb : p / 2 ∈ Set.Icc (0 : ℝ) 1 :=
      Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
    have hlt : (0 : ℝ) < p / 2 := by linarith
    have h1 := (hE _ hs _ hb).1 hlt
    simp only [postedPrice] at h1
    have hlt2 : p / 2 < p := by linarith
    have hcond2 : ¬ p ≤ p / 2 := not_le_of_gt hlt2
    have hcond : ¬ ((0 : ℝ) ≤ p ∧ p ≤ p / 2) := fun h => hcond2 h.2
    simp [hcond] at h1

end MathlibExt.GameTheory.MechanismDesign.BilateralTrade
