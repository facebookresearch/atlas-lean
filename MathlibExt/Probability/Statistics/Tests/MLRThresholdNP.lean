/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Choose.Basic
public import MathlibExt.Probability.Statistics.MonotoneLikelihoodRatio
public import MathlibExt.Probability.Statistics.NeymanPearson

/-!
# MLR threshold tests satisfy the Neyman–Pearson strict clauses

For a one-parameter family with a monotone likelihood ratio in a real statistic and
`θ₁ < θ₂`, with `k := L c θ₂ / L c θ₁` (which needs `0 < L c θ₁`) the threshold test at
`c` rejects at `n` wherever `L n θ₂` strictly exceeds `k * L n θ₁` and accepts wherever
it is strictly below. The comparisons are cross-multiplied: they never divide by
`L n θ₁`, so they stay meaningful when `L n θ₁ = 0` (extended-zero convention — a
strictly positive `L n θ₂` against a zero `L n θ₁` counts as exceeding every finite
threshold). At exact equality (`k * L n θ₁ = L n θ₂`) no condition is imposed: neither
clause fires.
Composite uniformity over all pairs is a separate gated follow-up.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory Real Set

open scoped Nat

/-- **MLR threshold tests satisfy the Neyman–Pearson strict clauses.** For a family with a
monotone likelihood ratio on `S` and `θ₁ < θ₂` in `S`, with `k := L c θ₂ / L c θ₁` (which
needs `0 < L c θ₁`), the threshold test at `c` rejects at `n` wherever `L n θ₂` strictly
exceeds `k * L n θ₁` and accepts wherever it is strictly below. The comparisons are
cross-multiplied, so they stay meaningful when `L n θ₁ = 0` (extended-zero convention);
at exact equality no condition is imposed. -/
theorem mlr_threshold_np_clauses (L : ℕ → ℝ → ℝ) (S : Set ℝ)
    (hMLR : HasMonotoneLikelihoodRatioOn L S)
    {θ₁ θ₂ : ℝ} (h₁ : θ₁ ∈ S) (h₂ : θ₂ ∈ S) (hlt : θ₁ < θ₂)
    (c : ℕ) (hc : 0 < L c θ₁) :
    0 ≤ L c θ₂ / L c θ₁ ∧
      (∀ n, (L c θ₂ / L c θ₁) * L n θ₁ < L n θ₂ → c < n) ∧
      (∀ n, L n θ₂ < (L c θ₂ / L c θ₁) * L n θ₁ → n < c) := by
  refine ⟨div_nonneg (hMLR.1 c θ₂ h₂) hc.le, ?_, ?_⟩
  · intro n h
    by_contra hcon
    rw [not_lt] at hcon
    have hTP2 := hMLR.2 hcon h₁ h₂ hlt.le
    rw [div_mul_eq_mul_div₀, div_lt_iff₀ hc] at h
    rw [mul_comm (L c θ₁) (L n θ₂), mul_comm (L n θ₁) (L c θ₂)] at hTP2
    linarith
  · intro n h
    by_contra hcon
    rw [not_lt] at hcon
    have hTP2 := hMLR.2 hcon h₁ h₂ hlt.le
    rw [div_mul_eq_mul_div₀, lt_div_iff₀ hc] at h
    rw [mul_comm (L n θ₁) (L c θ₂), mul_comm (L c θ₁) (L n θ₂)] at hTP2
    linarith

end ProbabilityTheory
