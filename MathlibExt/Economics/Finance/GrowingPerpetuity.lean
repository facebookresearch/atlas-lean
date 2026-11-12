/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Finance.DatedCashFlow
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Growing perpetuity

A growing perpetuity pays `C₁ (1 + g) ^ t` at date `t + 1`, discounted by
`discountFactor r (t + 1)`. With ratio `x = (1 + g) / (1 + r)`, `0 < 1 + r` and `0 ≤ x < 1`,
the discounted flows are summable with sum `C₁ / (r - g)` (Gordon growth formula).

## Main results

* `MathlibExt.Economics.Finance.hasSum_growingPerpetuity`: summability with sum
  `C₁ / (r - g)` (Mathlib `hasSum_geometric_of_lt_one`, `HasSum.mul_left`).
* `MathlibExt.Economics.Finance.growingPerpetuity_eq`: the `tsum` value.

The hypotheses are exactly the roadmap's `1 + r > 0` and `0 ≤ (1 + g) / (1 + r) < 1`; they
force `r - g > 0`. `g = -1` (only the first payment) is allowed.

## References

OpenStax, *Principles of Finance* (stock valuation, constant growth); SOA Exam FM syllabus.
Atlas roadmap target FI01.T03.
-/

@[expose] public section

namespace MathlibExt.Economics.Finance

/-- Discounted cash flow of a growing perpetuity: the payment `C₁ (1 + g) ^ t`
made at date `t + 1` (so `C₁` at date 1, growing at rate `g` per period),
discounted at the constant rate `r` (source clause: "cash flow `C_t = C₁ (1+g)^(t-1)`
at dates `t ≥ 1`"). -/
noncomputable def growingPerpetuityTerm (C₁ r g : ℝ) (t : ℕ) : ℝ :=
  discountFactor r (t + 1) * (C₁ * (1 + g) ^ t)

/-- Value of a growing perpetuity, the sum of all discounted cash flows. -/
noncomputable def growingPerpetuity (C₁ r g : ℝ) : ℝ :=
  ∑' t : ℕ, growingPerpetuityTerm C₁ r g t

/-- The discounted cash flows of a growing perpetuity are summable with sum
`C₁ / (r - g)` when `1 + r > 0` and `0 ≤ (1 + g) / (1 + r) < 1`
(Atlas roadmap FI01.T03). -/
theorem hasSum_growingPerpetuity (C₁ r g : ℝ) (hr : 0 < 1 + r)
    (hx₀ : 0 ≤ (1 + g) / (1 + r)) (hx₁ : (1 + g) / (1 + r) < 1) :
    HasSum (growingPerpetuityTerm C₁ r g) (C₁ / (r - g)) := by
  have h1r : (1 + r) ≠ 0 := ne_of_gt hr
  have hlt : (1 + g) < (1 + r) := (div_lt_one hr).mp hx₁
  have hpos : (0:ℝ) < r - g := by linarith
  have hrg : (r - g) ≠ 0 := ne_of_gt hpos
  have hterm : ∀ t : ℕ, growingPerpetuityTerm C₁ r g t
      = (C₁ / (1 + r)) * ((1 + g) / (1 + r)) ^ t := by
    intro t
    have hpowt : ((1 + r) ^ t) ≠ 0 := pow_ne_zero _ h1r
    have hprodt : ((1 + r) ^ t * (1 + r)) ≠ 0 := mul_ne_zero hpowt h1r
    simp only [growingPerpetuityTerm, discountFactor, div_pow]
    rw [pow_succ]
    field_simp
  have hx_eq : (1:ℝ) - (1 + g) / (1 + r) = (r - g) / (1 + r) := by
    field_simp
    ring
  have hfinal : C₁ / (1 + r) * (1 - (1 + g) / (1 + r))⁻¹ = C₁ / (r - g) := by
    rw [hx_eq, inv_div]
    field_simp
  have hgeom : HasSum (fun t : ℕ => ((1 + g) / (1 + r)) ^ t)
      (1 - (1 + g) / (1 + r))⁻¹ :=
    hasSum_geometric_of_lt_one hx₀ hx₁
  have hmul := hgeom.mul_left (C₁ / (1 + r))
  rw [hfinal] at hmul
  have hfun : growingPerpetuityTerm C₁ r g
      = fun t : ℕ => (C₁ / (1 + r)) * ((1 + g) / (1 + r)) ^ t := funext hterm
  rw [hfun]
  exact hmul

/-- Gordon growth formula: a growing perpetuity is worth `C₁ / (r - g)` under the
same hypotheses (Atlas roadmap FI01.T03). -/
theorem growingPerpetuity_eq (C₁ r g : ℝ) (hr : 0 < 1 + r)
    (hx₀ : 0 ≤ (1 + g) / (1 + r)) (hx₁ : (1 + g) / (1 + r) < 1) :
    growingPerpetuity C₁ r g = C₁ / (r - g) := by
  unfold growingPerpetuity
  exact (hasSum_growingPerpetuity C₁ r g hr hx₀ hx₁).tsum_eq

end MathlibExt.Economics.Finance
