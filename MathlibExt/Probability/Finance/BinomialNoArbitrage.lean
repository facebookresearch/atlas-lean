/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Finance.BinomialReplication
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# One-step no-arbitrage in the binomial model

In the one-step bond/stock model (stock price `S₀` today, `u * S₀` in the up state and
`d * S₀` in the down state; bond price `1` today, `R` at expiry), a portfolio `(Δ, B)`
is an arbitrage when it costs at most `0`, pays nonnegative amounts in both states, and
pays a positive amount in one state. There is no such arbitrage iff `d < R < u`, iff
the risk-neutral up probability `rnProb u d R = (R - d) / (u - d)` lies in `(0, 1)`.

## Main results

* `IsOneStepArbitrage`, `NoOneStepArbitrage`: the one-step arbitrage predicates.
* `noOneStepArbitrage_iff`: no arbitrage iff `d < R < u`.
* `rnProb_mem_Ioo_iff`, `noOneStepArbitrage_iff_rnProb`: the risk-neutral-probability form.

## References

* J. C. Cox, S. A. Ross, M. Rubinstein, *Option pricing: a simplified approach*,
  J. Financial Economics 7 (1979), 229–263.
* S. E. Shreve, *Stochastic Calculus for Finance I: The Binomial Asset Pricing Model*,
  Springer (2004), Chapter 1.
-/

@[expose] public section

namespace MathlibExt.Probability.Finance.BinomialNoArbitrage

open MathlibExt.Probability.Finance.BinomialReplication

/-- A one-step arbitrage in the bond/stock model: holdings `Δ` shares of stock and `B` units
of the bond (bond price `1` today, `R` at expiry; stock price `S₀` today, `u * S₀` in the
up state and `d * S₀` in the down state). The portfolio costs `Δ * S₀ + B` today, pays
`Δ * (u * S₀) + B * R` in the up state and `Δ * (d * S₀) + B * R` in the down state. It
is an arbitrage when the cost is nonpositive, both payoffs are nonnegative, and one payoff
is positive (source clause: "no arbitrage = no riskless profit"). -/
def IsOneStepArbitrage (S₀ u d R : ℝ) (Δ B : ℝ) : Prop :=
  Δ * S₀ + B ≤ 0 ∧ 0 ≤ Δ * (u * S₀) + B * R ∧ 0 ≤ Δ * (d * S₀) + B * R ∧
    (0 < Δ * (u * S₀) + B * R ∨ 0 < Δ * (d * S₀) + B * R)

/-- No arbitrage in the one-step bond/stock model: no holdings form a one-step arbitrage. -/
def NoOneStepArbitrage (S₀ u d R : ℝ) : Prop :=
  ¬ ∃ Δ B, IsOneStepArbitrage S₀ u d R Δ B

/-- **One-step no-arbitrage condition** (Atlas roadmap FI12.T01). For `S₀ > 0` and `0 < d < u`,
there is no one-step arbitrage iff `d < R < u`.

Proof route (not mandatory): if `R ≤ d`, `(Δ, B) = (1, -S₀)` is an arbitrage (cost `0`,
payoffs `(u - R) * S₀ ≥ 0` and `(d - R) * S₀ ≥ 0`, one of them positive since `d < u`);
if `u ≤ R`, `(Δ, B) = (-1, S₀)` is an arbitrage. Conversely, if `d < R < u`, the
risk-neutral weights `q = (R - d) / (u - d)` and `1 - q` are both positive, and the
`q`-weighted payoff of any portfolio is `R * (Δ * S₀ + B)` (since
`q * u + (1 - q) * d = R`), so a nonpositive-cost portfolio with nonnegative payoffs, one
positive, would have both a positive and a nonpositive `q`-weighted payoff: contradiction.
Use `linarith`/`nlinarith`; do not reprove the FTAP (this is a direct two-state argument). -/
theorem noOneStepArbitrage_iff {S₀ u d R : ℝ} (hS₀ : 0 < S₀) (hd0 : 0 < d) (hdu : d < u) :
    NoOneStepArbitrage S₀ u d R ↔ d < R ∧ R < u := by
  constructor
  · intro hNA
    rcases lt_or_ge d R with hdr | hRd
    · rcases lt_or_ge R u with hRu | huR
      · exact ⟨hdr, hRu⟩
      · have hdR : d < R := lt_of_lt_of_le hdu huR
        exfalso
        apply hNA
        refine ⟨-1, S₀, ?_, ?_, ?_, ?_⟩
        · have hcost : (-1 : ℝ) * S₀ + S₀ = 0 := by ring
          linarith
        · have hup : (-1 : ℝ) * (u * S₀) + S₀ * R = S₀ * (R - u) := by ring
          have hnn : 0 ≤ S₀ * (R - u) :=
            mul_nonneg (le_of_lt hS₀) (sub_nonneg.mpr huR)
          linarith
        · have hdown : (-1 : ℝ) * (d * S₀) + S₀ * R = S₀ * (R - d) := by ring
          have hnn : 0 ≤ S₀ * (R - d) :=
            mul_nonneg (le_of_lt hS₀) (sub_nonneg.mpr (le_of_lt hdR))
          linarith
        · right
          have hdown : (-1 : ℝ) * (d * S₀) + S₀ * R = S₀ * (R - d) := by ring
          have hpos : 0 < S₀ * (R - d) := mul_pos hS₀ (sub_pos.mpr hdR)
          linarith
    · have hRu : R < u := lt_of_le_of_lt hRd hdu
      exfalso
      apply hNA
      refine ⟨1, -S₀, ?_, ?_, ?_, ?_⟩
      · have hcost : (1 : ℝ) * S₀ + -S₀ = 0 := by ring
        linarith
      · have hup : (1 : ℝ) * (u * S₀) + -S₀ * R = S₀ * (u - R) := by ring
        have hnn : 0 ≤ S₀ * (u - R) :=
          mul_nonneg (le_of_lt hS₀) (sub_nonneg.mpr (le_of_lt hRu))
        linarith
      · have hdown : (1 : ℝ) * (d * S₀) + -S₀ * R = S₀ * (d - R) := by ring
        have hnn : 0 ≤ S₀ * (d - R) :=
          mul_nonneg (le_of_lt hS₀) (sub_nonneg.mpr hRd)
        linarith
      · left
        have hup : (1 : ℝ) * (u * S₀) + -S₀ * R = S₀ * (u - R) := by ring
        have hpos : 0 < S₀ * (u - R) := mul_pos hS₀ (sub_pos.mpr hRu)
        linarith
  · rintro ⟨hdr, hRu⟩
    rintro ⟨Δ, B, hc, hu, hd, hpos⟩
    have hmem : 0 < rnProb u d R ∧ rnProb u d R < 1 := by
      have hud : 0 < u - d := sub_pos.mpr hdu
      unfold rnProb
      rw [div_pos_iff_of_pos_right hud, div_lt_one hud]
      constructor <;> linarith
    obtain ⟨hq, hq1⟩ := hmem
    have hq1' : 0 < 1 - rnProb u d R := sub_pos.mpr hq1
    have hR0 : 0 < R := lt_trans hd0 hdr
    have hud_ne : u - d ≠ 0 := ne_of_gt (sub_pos.mpr hdu)
    have hqmul : rnProb u d R * (u - d) = R - d := by
      unfold rnProb
      exact div_mul_cancel₀ _ hud_ne
    have hkey : rnProb u d R * u + (1 - rnProb u d R) * d = R := by
      linear_combination hqmul
    have hweighted : rnProb u d R * (Δ * (u * S₀) + B * R) +
        (1 - rnProb u d R) * (Δ * (d * S₀) + B * R) = R * (Δ * S₀ + B) := by
      linear_combination Δ * S₀ * hkey
    have hle : R * (Δ * S₀ + B) ≤ 0 := by
      have h := mul_le_mul_of_nonneg_left hc (le_of_lt hR0)
      simpa using h
    have hgt : 0 < rnProb u d R * (Δ * (u * S₀) + B * R) +
        (1 - rnProb u d R) * (Δ * (d * S₀) + B * R) := by
      rcases hpos with h | h
      · exact add_pos_of_pos_of_nonneg (mul_pos hq h) (mul_nonneg (le_of_lt hq1') hd)
      · exact add_pos_of_nonneg_of_pos (mul_nonneg (le_of_lt hq) hu) (mul_pos hq1' h)
    rw [hweighted] at hgt
    linarith

/-- The risk-neutral up probability lies in `(0, 1)` exactly when `d < R < u`. -/
theorem rnProb_mem_Ioo_iff {u d R : ℝ} (hdu : d < u) :
    0 < rnProb u d R ∧ rnProb u d R < 1 ↔ d < R ∧ R < u := by
  have hud : 0 < u - d := sub_pos.mpr hdu
  unfold rnProb
  rw [div_pos_iff_of_pos_right hud, div_lt_one hud]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- **No arbitrage iff the risk-neutral probability is a probability.** The bridge to the
landed one-step binomial model: no-arbitrage holds iff `rnProb u d R ∈ (0, 1)`. -/
theorem noOneStepArbitrage_iff_rnProb {S₀ u d R : ℝ} (hS₀ : 0 < S₀) (hd0 : 0 < d)
    (hdu : d < u) :
    NoOneStepArbitrage S₀ u d R ↔ 0 < rnProb u d R ∧ rnProb u d R < 1 := by
  rw [noOneStepArbitrage_iff hS₀ hd0 hdu, rnProb_mem_Ioo_iff hdu]

end MathlibExt.Probability.Finance.BinomialNoArbitrage
