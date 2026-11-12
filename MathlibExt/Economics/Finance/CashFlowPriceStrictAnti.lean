/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Finance.DatedCashFlow
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith

/-!
# Price of a cash-flow stream is strictly decreasing in a common yield

The price of a nonnegative future cash-flow stream at a common yield `r` is the
FI01 present value `∑ t ∈ s, discountFactor r t * c t`. Each term is antitone
in `r` on `(-1, ∞)`, and a positive payment at a date `t ≥ 1` makes its term
strictly decreasing, so the sum is strictly decreasing.

## Main results

* `MathlibExt.Economics.Finance.strictAntiOn_cashFlowPrice`: the price is
  `StrictAntiOn` `Set.Ioi (-1)` (`Finset.sum_lt_sum`, `pow_lt_pow_left₀`,
  `inv_lt_inv₀`). This is the bond / present-value form over an arbitrary
  finite payment set; FI02.T02 `strictAntiOn_npv` is the separate NPV form
  over the fixed dates `range (N + 1)`.

## References

SOA Exam FM syllabus (price/yield); OpenStax, *Principles of Finance*, time
value of money. Atlas roadmap target FI03.T02.
-/

@[expose] public section

namespace MathlibExt.Economics.Finance

/-- Price of the cash-flow stream `c` paid at the dates `t ∈ s`, at a common
per-period yield `r`: the FI01 present value under the constant-rate discount
factors (source clause: "`P(r) = Σ_t c_t (1 + r)⁻ᵗ`"). -/
noncomputable def cashFlowPrice (c : ℕ → ℝ) (s : Finset ℕ) (r : ℝ) : ℝ :=
  presentValue (discountFactor r) s c

/-- With nonnegative payments and at least one positive payment at a date
`t ≥ 1`, the price is strictly decreasing in the yield on `(-1, ∞)`
(Atlas roadmap FI03.T02). The `1 ≤ t` condition is load-bearing: a positive
payment at `t = 0` alone is discounted by 1 at every yield. This is the bond /
present-value form over an arbitrary finite payment set; FI02.T02
`strictAntiOn_npv` is the separate NPV form over the fixed dates
`range (N + 1)`. -/
theorem strictAntiOn_cashFlowPrice {c : ℕ → ℝ} {s : Finset ℕ}
    (hnn : ∀ t ∈ s, 0 ≤ c t)
    (hpos : ∃ t ∈ s, 1 ≤ t ∧ 0 < c t) :
    StrictAntiOn (cashFlowPrice c s) (Set.Ioi (-1)) := by
  obtain ⟨t₀, ht₀s, ht₀ge, ht₀pos⟩ := hpos
  intro r hr r' hr' hrr'
  rw [Set.mem_Ioi] at hr hr'
  have h1r : (0 : ℝ) < 1 + r := by linarith
  have h1r' : (0 : ℝ) < 1 + r' := by linarith
  have hle : (1 : ℝ) + r ≤ 1 + r' := by linarith
  have hlt : (1 : ℝ) + r < 1 + r' := by linarith
  unfold cashFlowPrice presentValue discountFactor
  apply Finset.sum_lt_sum
  · intro t ht
    have hpow : (1 + r) ^ t ≤ (1 + r') ^ t :=
      pow_le_pow_left₀ (le_of_lt h1r) hle t
    have hpost : (0 : ℝ) < (1 + r) ^ t := pow_pos h1r t
    have hinv : ((1 + r') ^ t)⁻¹ ≤ ((1 + r) ^ t)⁻¹ :=
      inv_anti₀ hpost hpow
    exact mul_le_mul_of_nonneg_right hinv (hnn t ht)
  · refine ⟨t₀, ht₀s, ?_⟩
    have hne : t₀ ≠ 0 := ne_of_gt ht₀ge
    have hpow : (1 + r) ^ t₀ < (1 + r') ^ t₀ :=
      pow_lt_pow_left₀ hlt (le_of_lt h1r) hne
    have hposr : (0 : ℝ) < (1 + r) ^ t₀ := pow_pos h1r t₀
    have hposr' : (0 : ℝ) < (1 + r') ^ t₀ := pow_pos h1r' t₀
    have hinv : ((1 + r') ^ t₀)⁻¹ < ((1 + r) ^ t₀)⁻¹ :=
      (inv_lt_inv₀ hposr' hposr).mpr hpow
    exact mul_lt_mul_of_pos_right hinv ht₀pos

end MathlibExt.Economics.Finance
