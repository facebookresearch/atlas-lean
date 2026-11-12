/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Sequential.Ville

/-!
# Tests for Ville's maximal inequality

Non-vacuity with the constant process `1` (the bound is attained at `a = 1`), the finite-horizon
running-maximum corollary, the `α`-level form for a nonnegative supermartingale started at `1`,
and the boundary check that a negative-valued process fails the nonnegativity hypothesis.
-/

@[expose] public section

open MeasureTheory

/-- Non-vacuity: the constant process `1` is a nonnegative supermartingale, so under a
probability measure the theorem gives `a · μ{∃ n, a ≤ 1} ≤ 1`; at `a = 1` both sides equal `1`,
so the bound is attained. Prove via `Supermartingale.ville_maximal_ineq` applied to
`(martingale_const 𝒢 μ 1).supermartingale`. -/
example {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝒢 : Filtration ℕ m0} {a : ℝ} (ha : 0 < a) :
    a * μ.real {ω | ∃ n : ℕ, a ≤ (fun (_ : ℕ) (_ : Ω) => (1 : ℝ)) n ω} ≤ 1 := by
  refine ((martingale_const 𝒢 μ (1 : ℝ)).supermartingale.ville_maximal_ineq
    (fun _ _ => zero_le_one) ha).trans_eq ?_
  simp

/-- Finite-horizon corollary, in Mathlib's `maximal_ineq` running-maximum form: the finite
event is contained in the countable crossing event. -/
example {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    {𝒢 : Filtration ℕ m0} {M : ℕ → Ω → ℝ}
    (hsup : Supermartingale M 𝒢 μ) (hnonneg : 0 ≤ M) {a : ℝ} (ha : 0 < a) (n : ℕ) :
    a * μ.real {ω | a ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      fun k => M k ω} ≤ ∫ ω, M 0 ω ∂μ := by
  refine le_trans (mul_le_mul_of_nonneg_left (measureReal_mono ?_) ha.le)
    (hsup.ville_maximal_ineq hnonneg ha)
  rintro ω (hω : a ≤ _)
  obtain ⟨k, -, hk⟩ := (Finset.le_sup'_iff _).1 hω
  exact ⟨k, hk⟩

/-- The `α`-level form used by later slices: a nonnegative supermartingale started at `1`
crosses `1 / α` with probability at most `α`. -/
example {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝒢 : Filtration ℕ m0} {E : ℕ → Ω → ℝ}
    (hsup : Supermartingale E 𝒢 μ) (hnonneg : 0 ≤ E) (hstart : ∀ ω, E 0 ω = 1)
    {α : ℝ} (hα : 0 < α) :
    μ.real {ω | ∃ n, 1 / α ≤ E n ω} ≤ α := by
  have h := hsup.ville_maximal_ineq hnonneg (one_div_pos.2 hα)
  have h1 : ∫ ω, E 0 ω ∂μ = 1 := by simp [hstart]
  calc μ.real {ω | ∃ n, 1 / α ≤ E n ω}
      = α * (1 / α * μ.real {ω | ∃ n, 1 / α ≤ E n ω}) := by
        rw [← mul_assoc, mul_one_div_cancel hα.ne', one_mul]
    _ ≤ α * 1 := mul_le_mul_of_nonneg_left (h.trans_eq h1) hα.le
    _ = α := mul_one α

/-- Boundary: a process taking negative values does not satisfy the nonnegativity hypothesis,
so martingales such as a symmetric random walk are outside the theorem's scope. -/
example : ¬ (0 ≤ fun (_ : ℕ) (_ : Unit) => (-1 : ℝ)) := by
  intro h
  have := h 0 ()
  norm_num at this
