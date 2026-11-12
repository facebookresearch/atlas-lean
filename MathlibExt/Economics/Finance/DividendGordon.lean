/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Finance.GrowingPerpetuity
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Tactic

/-!
# Gordon formula for constant-growth dividends

Dividends are date-indexed: `dividendStream D₁ g t` is the dividend paid at date `t`
(`0` at date `0`, `D₁ * (1 + g) ^ (t - 1)` for `t ≥ 1`). Discounting gives
`discountedDividendStream`, whose shift by one date is exactly the landed
growing-perpetuity stream, so the Gordon formula `D₁ / (r - g)` follows from
`MathlibExt.Economics.Finance.hasSum_growingPerpetuity` (FI01.T03) by a shift plus
identification, without reproving the geometric series.

## Main results

* `MathlibExt.Economics.Finance.DividendGordon.dividendStream`: date-indexed dividend stream.
* `MathlibExt.Economics.Finance.DividendGordon.discountedDividendStream`: discounted
  dividend stream.
* `MathlibExt.Economics.Finance.DividendGordon.discountedDividendStream_succ`: shifting by
  one date gives the growing-perpetuity stream.
* `MathlibExt.Economics.Finance.DividendGordon.dividendGordon_of_hasSumGrowing`: the
  dividend-stream identification.
* `MathlibExt.Economics.Finance.DividendGordon.dividendGordon`: the Gordon `HasSum`.
* `MathlibExt.Economics.Finance.DividendGordon.dividendGordon_tsum`: the `tsum` form.

## References

OpenStax, *Principles of Finance* (stock valuation, constant growth); SOA Exam FM syllabus.
Atlas roadmap target FI14.T03.
-/

@[expose] public section

namespace MathlibExt.Economics.Finance.DividendGordon


open MathlibExt.Economics.Finance

/-- Dividend stream with first dividend `D₁` at date 1, growing at rate `g` per period.
`dividendStream D₁ g t` is the dividend paid at date `t`: `0` today (`t = 0`, no
dividend is paid at date 0) and `D₁ * (1 + g) ^ (t - 1)` for `t ≥ 1` (source clause:
"dividend `D_t = D₁ (1+g)^{t-1}` at dates `t ≥ 1`"). This is a genuinely date-indexed
dividend abstraction, distinct from the growing-perpetuity stream, which is indexed
from `0` at date 1. -/
noncomputable def dividendStream (D₁ g : ℝ) : ℕ → ℝ :=
  fun t => if t = 0 then 0 else D₁ * (1 + g) ^ (t - 1)

/-- Discounted dividend stream at rate `r`: `discountFactor r t * dividendStream D₁ g t`
(source clause: "discounted dividend at date `t`"). -/
noncomputable def discountedDividendStream (D₁ r g : ℝ) : ℕ → ℝ :=
  fun t => discountFactor r t * dividendStream D₁ g t

/-- Shifting the discounted dividend stream by one date gives exactly the
growing-perpetuity stream: at date `t + 1` the dividend is `D₁ * (1 + g) ^ t`,
discounted by `discountFactor r (t + 1)`. -/
theorem discountedDividendStream_succ (D₁ r g : ℝ) (t : ℕ) :
    discountedDividendStream D₁ r g (t + 1) = growingPerpetuityTerm D₁ r g t := by
  have hne : t + 1 ≠ 0 := by omega
  unfold discountedDividendStream dividendStream growingPerpetuityTerm
  rw [ite_eq_right hne, Nat.add_sub_cancel]

/-- **Dividend stream identification.** The discounted dividend stream has the same
`HasSum` as the growing-perpetuity stream: shift by one date
(`hasSum_nat_add_iff'` at `k = 1`, using that the date-`0` term is `0`), then apply the
shift lemma `discountedDividendStream_succ`. This is the specialization step: it cites
`hasSum_growingPerpetuity` (FI01.T03) and does not reprove the geometric series. -/
theorem dividendGordon_of_hasSumGrowing {D₁ r g : ℝ}
    (h : HasSum (growingPerpetuityTerm D₁ r g) (D₁ / (r - g))) :
    HasSum (discountedDividendStream D₁ r g) (D₁ / (r - g)) := by
  have hfun : (fun n => discountedDividendStream D₁ r g (n + 1))
      = growingPerpetuityTerm D₁ r g :=
    funext (fun t => discountedDividendStream_succ D₁ r g t)
  have h0 : discountedDividendStream D₁ r g 0 = 0 := by
    simp [discountedDividendStream, dividendStream]
  have h' : HasSum (fun n => discountedDividendStream D₁ r g (n + 1)) (D₁ / (r - g)) := by
    rw [hfun]
    exact h
  have hsum0 : ∑ i ∈ Finset.range 1, discountedDividendStream D₁ r g i = 0 := by
    simp [h0]
  have hiff := hasSum_nat_add_iff' (f := discountedDividendStream D₁ r g) (g := D₁ / (r - g)) 1
  rw [hsum0, sub_zero] at hiff
  exact hiff.mp h'

/-- **Gordon formula for constant-growth dividends.** With `1 + r > 0` and the growth
ratio `(1 + g) / (1 + r)` in `[0, 1)` (source clauses: "constant admissible dividend
growth", "Gordon formula"), the infinite sum of discounted dividends is `D₁ / (r - g)`. -/
theorem dividendGordon {D₁ r g : ℝ} (hr : 0 < 1 + r)
    (hx₀ : 0 ≤ (1 + g) / (1 + r)) (hx₁ : (1 + g) / (1 + r) < 1) :
    HasSum (discountedDividendStream D₁ r g) (D₁ / (r - g)) := by
  exact dividendGordon_of_hasSumGrowing (hasSum_growingPerpetuity D₁ r g hr hx₀ hx₁)

/-- The `tsum` form of the Gordon formula for constant-growth dividends. -/
theorem dividendGordon_tsum {D₁ r g : ℝ} (hr : 0 < 1 + r)
    (hx₀ : 0 ≤ (1 + g) / (1 + r)) (hx₁ : (1 + g) / (1 + r) < 1) :
    ∑' t, discountedDividendStream D₁ r g t = D₁ / (r - g) := by
  exact (dividendGordon hr hx₀ hx₁).tsum_eq


end MathlibExt.Economics.Finance.DividendGordon
