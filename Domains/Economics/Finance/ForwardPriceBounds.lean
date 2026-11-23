/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# No-arbitrage bounds for a forward price under frictions

A one-period forward market where the underlying is bought at the ask and sold short at the
bid, cash is lent at a gross rate `lendRate` and borrowed at `borrowRate`, and one unit pays a
known income at maturity. Static hedged strategies combine purchases, short sales, lending,
borrowing and a forward position with zero net exposure to the terminal spot price; an
arbitrage has nonnegative cash flows at both dates and a positive one at some date. With
`0 < bid ≤ ask` and `0 < lendRate ≤ borrowRate`, there is no arbitrage iff
`bid * lendRate - income ≤ forwardPrice ≤ ask * borrowRate - income`: frictions give an interval
rather than the single cost-of-carry price `S * R - income`, to which it collapses without them.

## Main results

* `cashAndCarry_isArbitrage`, `reverseCashAndCarry_isArbitrage`: the explicit arbitrages above
  and below the interval.
* `not_exists_isArbitrage_iff`: the no-arbitrage interval.
* `not_exists_isArbitrage_iff_frictionless`: without frictions the interval is one price.

## References

* J. C. Hull, *Options, Futures, and Other Derivatives*, Chapter 5 (forward prices, cost of
  carry, unequal borrowing and lending rates).
-/

@[expose] public section

namespace MathlibExt.Probability.Finance.ForwardPriceBounds

/-- A one-period forward market with frictions. The underlying can be bought at the ask and sold
short at the bid; cash is lent at the gross rate `lendRate` and borrowed at the gross rate
`borrowRate` over the forward's life; one unit of the underlying pays the known income `income`
at maturity (a deterministic dividend or carry, paid by a short seller to the lender of the
asset); `forwardPrice` is the delivery price of a forward contract on one unit, of the same
maturity and unit. -/
structure ForwardMarket where
  /-- Spot bid price: proceeds per unit sold short. -/
  bid : ℝ
  /-- Spot ask price: cost per unit bought. -/
  ask : ℝ
  /-- Gross lending rate over the period. -/
  lendRate : ℝ
  /-- Gross borrowing rate over the period. -/
  borrowRate : ℝ
  /-- Known income per unit of the underlying paid at maturity. -/
  income : ℝ
  /-- Forward (delivery) price per unit. -/
  forwardPrice : ℝ

/-- A static trading strategy: `buy` units bought at the ask, `sell` units sold short at the bid,
`lend` cash lent, `borrow` cash borrowed, and a long forward position of `fwd` units (short when
negative). -/
structure Strategy where
  /-- Units of the underlying bought at the ask. -/
  buy : ℝ
  /-- Units of the underlying sold short at the bid. -/
  sell : ℝ
  /-- Cash lent. -/
  lend : ℝ
  /-- Cash borrowed. -/
  borrow : ℝ
  /-- Long forward position (units; negative means short). -/
  fwd : ℝ

/-- A strategy is admissible when trade sizes are nonnegative and it is hedged: the net
underlying exposure at maturity, `buy - sell + fwd`, is zero, so its payoff does not depend on
the terminal spot price. -/
def Strategy.IsAdmissible (s : Strategy) : Prop :=
  0 ≤ s.buy ∧ 0 ≤ s.sell ∧ 0 ≤ s.lend ∧ 0 ≤ s.borrow ∧ s.buy - s.sell + s.fwd = 0

/-- Cash received at time `0`: short-sale proceeds and borrowing, minus purchases and lending
(forwards cost nothing to enter). -/
def initialCashFlow (M : ForwardMarket) (s : Strategy) : ℝ :=
  M.bid * s.sell + s.borrow - M.ask * s.buy - s.lend

/-- Cash received at maturity by a hedged strategy: net income on the underlying position, loan
repayments received and paid, and the forward's delivery payment `- fwd * forwardPrice` (the
terminal spot value `(buy - sell + fwd) * S_T` vanishes for a hedged strategy). -/
def terminalCashFlow (M : ForwardMarket) (s : Strategy) : ℝ :=
  (s.buy - s.sell) * M.income + M.lendRate * s.lend - M.borrowRate * s.borrow -
    s.fwd * M.forwardPrice

/-- An arbitrage is an admissible strategy with nonnegative cash flows at both dates and a
positive cash flow at one of them. -/
def IsArbitrage (M : ForwardMarket) (s : Strategy) : Prop :=
  s.IsAdmissible ∧ 0 ≤ initialCashFlow M s ∧ 0 ≤ terminalCashFlow M s ∧
    (0 < initialCashFlow M s ∨ 0 < terminalCashFlow M s)

/-- Cash-and-carry: above the upper bound `ask * borrowRate - income`, borrowing the ask price,
buying one unit and selling it forward is an arbitrage. -/
theorem cashAndCarry_isArbitrage (M : ForwardMarket) (hask : 0 ≤ M.ask)
    (hF : M.ask * M.borrowRate - M.income < M.forwardPrice) :
    IsArbitrage M ⟨1, 0, 0, M.ask, -1⟩ := by
  have hadm : Strategy.IsAdmissible ⟨1, 0, 0, M.ask, -1⟩ := by
    change 0 ≤ (1 : ℝ) ∧ 0 ≤ (0 : ℝ) ∧ 0 ≤ (0 : ℝ) ∧ 0 ≤ M.ask ∧ (1 : ℝ) - 0 + -1 = 0
    exact ⟨by norm_num, by norm_num, by norm_num, hask, by norm_num⟩
  have hc0 : initialCashFlow M ⟨1, 0, 0, M.ask, -1⟩ = 0 := by
    change M.bid * 0 + M.ask - M.ask * 1 - (0 : ℝ) = 0
    ring
  have hc1 : terminalCashFlow M ⟨1, 0, 0, M.ask, -1⟩
      = M.forwardPrice - (M.ask * M.borrowRate - M.income) := by
    change ((1 : ℝ) - 0) * M.income + M.lendRate * 0 - M.borrowRate * M.ask -
      -1 * M.forwardPrice = _
    ring
  exact ⟨hadm, hc0.ge, by rw [hc1]; linarith [hF], Or.inr (by rw [hc1]; linarith [hF])⟩

/-- Reverse cash-and-carry: below the lower bound `bid * lendRate - income`, shorting one unit,
lending the bid proceeds and buying forward is an arbitrage. -/
theorem reverseCashAndCarry_isArbitrage (M : ForwardMarket) (hbid : 0 ≤ M.bid)
    (hF : M.forwardPrice < M.bid * M.lendRate - M.income) :
    IsArbitrage M ⟨0, 1, M.bid, 0, 1⟩ := by
  have hadm : Strategy.IsAdmissible ⟨0, 1, M.bid, 0, 1⟩ := by
    change 0 ≤ (0 : ℝ) ∧ 0 ≤ (1 : ℝ) ∧ 0 ≤ M.bid ∧ 0 ≤ (0 : ℝ) ∧ (0 : ℝ) - 1 + 1 = 0
    exact ⟨by norm_num, by norm_num, hbid, by norm_num, by norm_num⟩
  have hc0 : initialCashFlow M ⟨0, 1, M.bid, 0, 1⟩ = 0 := by
    change M.bid * 1 + 0 - M.ask * 0 - M.bid = 0
    ring
  have hc1 : terminalCashFlow M ⟨0, 1, M.bid, 0, 1⟩
      = (M.bid * M.lendRate - M.income) - M.forwardPrice := by
    change ((0 : ℝ) - 1) * M.income + M.lendRate * M.bid - M.borrowRate * 0 -
      1 * M.forwardPrice = _
    ring
  exact ⟨hadm, hc0.ge, by rw [hc1]; linarith [hF], Or.inr (by rw [hc1]; linarith [hF])⟩

/-- **No-arbitrage interval.** With a positive bid not above the ask and a positive lending rate
not above the borrowing rate, there is no arbitrage iff the forward price lies in
`[bid * lendRate - income, ask * borrowRate - income]`. -/
theorem not_exists_isArbitrage_iff (M : ForwardMarket) (hbid : 0 < M.bid)
    (hspread : M.bid ≤ M.ask) (hlend : 0 < M.lendRate) (hrates : M.lendRate ≤ M.borrowRate) :
    (¬ ∃ s : Strategy, IsArbitrage M s) ↔
      M.bid * M.lendRate - M.income ≤ M.forwardPrice ∧
        M.forwardPrice ≤ M.ask * M.borrowRate - M.income := by
  constructor
  · intro hno
    rcases lt_or_ge M.forwardPrice (M.bid * M.lendRate - M.income) with h | h
    · exact absurd ⟨_, reverseCashAndCarry_isArbitrage M hbid.le h⟩ hno
    · rcases lt_or_ge (M.ask * M.borrowRate - M.income) M.forwardPrice with h' | h'
      · exact absurd ⟨_, cashAndCarry_isArbitrage M (le_trans hbid.le hspread) h'⟩ hno
      · exact ⟨h, h'⟩
  · intro hband hex
    obtain ⟨s, hsadm, hc0nn, hc1nn, hpos⟩ := hex
    obtain ⟨ha, hb, hL, hB, hhedge⟩ := hsadm
    set x : ℝ := M.income + M.forwardPrice with hxdef
    have hx_lb : M.bid * M.lendRate ≤ x := by rw [hxdef]; linarith [hband.1]
    have hx_ub : x ≤ M.ask * M.borrowRate := by rw [hxdef]; linarith [hband.2]
    have hx_pos : 0 < x := lt_of_lt_of_le (mul_pos hbid hlend) hx_lb
    have hSa : 0 < M.ask := lt_of_lt_of_le hbid hspread
    set μ : ℝ := max M.lendRate (x / M.ask) with hμdef
    have hμ1 : M.lendRate ≤ μ := le_max_left _ _
    have hμ2 : x / M.ask ≤ μ := le_max_right _ _
    have hμ3 : μ ≤ M.borrowRate := by
      rw [hμdef, max_le_iff]
      exact ⟨hrates, (div_le_iff₀ hSa).mpr (by rw [mul_comm]; exact hx_ub)⟩
    have hμ4 : μ ≤ x / M.bid := by
      rw [hμdef, max_le_iff]
      refine ⟨(le_div_iff₀ hbid).mpr (by rw [mul_comm]; exact hx_lb), ?_⟩
      apply (le_div_iff₀ hbid).mpr
      calc x / M.ask * M.bid ≤ x / M.ask * M.ask :=
            mul_le_mul_of_nonneg_left hspread (div_nonneg hx_pos.le hSa.le)
        _ = x := div_mul_cancel₀ x hSa.ne'
    have hx_le : x ≤ μ * M.ask := (div_le_iff₀ hSa).mp hμ2
    have hμx_le : μ * M.bid ≤ x := (le_div_iff₀ hbid).mp hμ4
    have hμpos : 0 < μ := lt_of_lt_of_le hlend hμ1
    have hf : s.fwd = s.sell - s.buy := by linarith [hhedge]
    have hkey : terminalCashFlow M s + μ * initialCashFlow M s =
        s.buy * (x - μ * M.ask) + s.sell * (μ * M.bid - x) +
        s.lend * (M.lendRate - μ) + s.borrow * (μ - M.borrowRate) := by
      unfold terminalCashFlow initialCashFlow
      rw [hf, hxdef]
      ring
    have h1 : s.buy * (x - μ * M.ask) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos ha (by linarith [hx_le])
    have h2 : s.sell * (μ * M.bid - x) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hb (by linarith [hμx_le])
    have h3 : s.lend * (M.lendRate - μ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hL (by linarith [hμ1])
    have h4 : s.borrow * (μ - M.borrowRate) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hB (by linarith [hμ3])
    have hsum : terminalCashFlow M s + μ * initialCashFlow M s ≤ 0 := by
      rw [hkey]
      linarith [h1, h2, h3, h4]
    have hμc0 : 0 ≤ μ * initialCashFlow M s := mul_nonneg hμpos.le hc0nn
    have hc1eq : terminalCashFlow M s = 0 := by linarith [hsum, hc1nn, hμc0]
    have hμc0eq : μ * initialCashFlow M s = 0 := by linarith [hsum, hc1nn, hμc0]
    have hc0eq : initialCashFlow M s = 0 :=
      (mul_eq_zero.mp hμc0eq).resolve_left (ne_of_gt hμpos)
    rcases hpos with h | h <;> linarith

/-- **Frictionless limit.** Without a bid-ask spread or a borrowing-lending wedge
(`bid = ask = S`, `lendRate = borrowRate = R`), the interval collapses to the single
cost-of-carry price `S * R - income`. -/
theorem not_exists_isArbitrage_iff_frictionless (M : ForwardMarket) {S R : ℝ} (hS : 0 < S)
    (hR : 0 < R) (hbid : M.bid = S) (hask : M.ask = S) (hlend : M.lendRate = R)
    (hborrow : M.borrowRate = R) :
    (¬ ∃ s : Strategy, IsArbitrage M s) ↔ M.forwardPrice = S * R - M.income := by
  have hbid' : 0 < M.bid := by rw [hbid]; exact hS
  have hspread' : M.bid ≤ M.ask := by rw [hbid, hask]
  have hlend' : 0 < M.lendRate := by rw [hlend]; exact hR
  have hrates' : M.lendRate ≤ M.borrowRate := by rw [hlend, hborrow]
  rw [not_exists_isArbitrage_iff M hbid' hspread' hlend' hrates', hbid, hask, hlend, hborrow]
  constructor
  · intro h
    exact le_antisymm h.2 h.1
  · intro h
    rw [h]
    exact ⟨le_refl _, le_refl _⟩

end MathlibExt.Probability.Finance.ForwardPriceBounds
