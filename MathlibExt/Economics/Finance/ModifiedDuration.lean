/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Finance.DatedCashFlow
public import MathlibExt.Economics.Finance.CashFlowPriceStrictAnti
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Modified duration and the price derivative

For fixed cash flows at a common yield `r`, the price is FI03.T02's
`cashFlowPrice c s r = ∑_{t∈s} c t * (1 + r)^(-t)`. Termwise differentiation
gives `P′(r) = -∑_{t∈s} t * c t * (1 + r)^(-t-1)`, so with modified duration
`Dmod = Macaulay / (1 + r)`, `P′(r) = -Dmod(r) * P(r)` when `P(r) ≠ 0`.

## Main results

* `MathlibExt.Economics.Finance.hasDerivAt_cashFlowPrice`: the termwise
  derivative (`HasDerivAt.fun_sum`, `hasDerivAt_zpow`, `HasDerivAt.comp`).
* `MathlibExt.Economics.Finance.deriv_cashFlowPrice_eq_neg_modifiedDuration_mul`:
  `P′(r) = -Dmod(r) * P(r)`.

The price is the existing `cashFlowPrice`; its zpow form, used to
differentiate termwise, is a private proof lemma. The theorems assume only
`-1 < r` and (for the `deriv` identity) `cashFlowPrice c s r ≠ 0`; no sign
hypothesis on the cash flows is needed. The roadmap's "fixed positive cash
flows" is the usual case giving `P > 0`.

## References

SOA Exam FM syllabus (modified duration). Atlas roadmap target FI04.T01.
-/

@[expose] public section

namespace MathlibExt.Economics.Finance

/-- Proof device: the zpow form `∑ t ∈ s, c t * (1 + r) ^ (-(t : ℤ))` of
`cashFlowPrice c s r`, for every `r` (`zpow_neg`, `zpow_natCast`). -/
private theorem cashFlowPrice_eq_zpow_sum (c : ℕ → ℝ) (s : Finset ℕ) :
    cashFlowPrice c s = fun r => ∑ t ∈ s, c t * (1 + r) ^ (-(t : ℤ)) := by
  funext r
  unfold cashFlowPrice presentValue discountFactor
  apply Finset.sum_congr rfl
  intro t _
  rw [zpow_neg, zpow_natCast, mul_comm]

/-- Macaulay duration: the payment-date-weighted average discount factor,
divided by the price `cashFlowPrice` (source clause: "Macaulay =
`Σ t * c_t (1+r)^(-t) / P`"). -/
noncomputable def macaulayDuration (c : ℕ → ℝ) (s : Finset ℕ) (r : ℝ) : ℝ :=
  (∑ t ∈ s, (t : ℝ) * c t * (1 + r) ^ (-(t : ℤ))) / cashFlowPrice c s r

/-- Modified duration: Macaulay duration divided by `1 + r`
(source clause: "`Dmod = Macaulay / (1 + r)`"). -/
noncomputable def modifiedDuration (c : ℕ → ℝ) (s : Finset ℕ) (r : ℝ) : ℝ :=
  macaulayDuration c s r / (1 + r)

/-- Termwise derivative of the price `cashFlowPrice` at a common yield above `-1`
(Atlas roadmap FI04.T01). -/
theorem hasDerivAt_cashFlowPrice {c : ℕ → ℝ} {s : Finset ℕ} {r : ℝ} (hr : -1 < r) :
    HasDerivAt (cashFlowPrice c s)
      (-∑ t ∈ s, (t : ℝ) * c t * (1 + r) ^ (-(t : ℤ) - 1)) r := by
  have h1pos : (0 : ℝ) < 1 + r := by linarith
  have h1ne : (1 : ℝ) + r ≠ 0 := ne_of_gt h1pos
  have h_inner : HasDerivAt (fun r : ℝ => 1 + r) 1 r :=
    HasDerivAt.const_add 1 (hasDerivAt_id' r)
  rw [cashFlowPrice_eq_zpow_sum, ← Finset.sum_neg_distrib]
  apply HasDerivAt.fun_sum
  intro t ht
  have h_outer := hasDerivAt_zpow (-(t : ℤ)) (1 + r) (Or.inl h1ne)
  have h_chain := h_outer.comp r h_inner
  have h_chain' : HasDerivAt (fun y : ℝ => (1 + y) ^ (-(t : ℤ))) _ r := h_chain
  simp only [mul_one] at h_chain'
  have h_mul := HasDerivAt.const_mul (c t) h_chain'
  convert h_mul using 2
  push_cast
  ring

/-- `P′(r) = -Dmod(r) * P(r)` for the price `cashFlowPrice` at a nonzero price
(Atlas roadmap FI04.T01). -/
theorem deriv_cashFlowPrice_eq_neg_modifiedDuration_mul {c : ℕ → ℝ} {s : Finset ℕ}
    {r : ℝ} (hr : -1 < r) (hP : cashFlowPrice c s r ≠ 0) :
    deriv (cashFlowPrice c s) r = -modifiedDuration c s r * cashFlowPrice c s r := by
  have h1pos : (0 : ℝ) < 1 + r := by linarith
  have h1ne : (1 : ℝ) + r ≠ 0 := ne_of_gt h1pos
  rw [(hasDerivAt_cashFlowPrice hr).deriv]
  unfold modifiedDuration macaulayDuration
  have hz : ∀ t : ℕ, (1 + r : ℝ) ^ (-(t : ℤ) - 1) = (1 + r) ^ (-(t : ℤ)) * (1 + r)⁻¹ := by
    intro t
    have heq : (-(t : ℤ) - 1 : ℤ) = -(t : ℤ) + (-1) := by ring
    rw [heq, zpow_add₀ h1ne, zpow_neg_one]
  simp_rw [hz]
  have hterm : ∀ t : ℕ, (t : ℝ) * c t * ((1 + r) ^ (-(t : ℤ)) * (1 + r)⁻¹)
      = ((t : ℝ) * c t * (1 + r) ^ (-(t : ℤ))) * (1 + r)⁻¹ := by
    intro t; ring
  simp_rw [hterm, ← Finset.sum_mul]
  field_simp

end MathlibExt.Economics.Finance
