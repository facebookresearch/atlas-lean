/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Probability.ProbabilityMassFunction.Basic

@[expose] public section

/-! # Le Cam's two-point bound

For two distributions on a finite type and any test, the sum of
the two error probabilities is at least `1` minus the total
variation distance. This is the two-point core of roadmap package
ML-29 of the Atlas TCS canon roadmap; Fano's method (ML-30) and
the KL corollaries are follow-ups.

Source: Tsybakov, Introduction to Nonparametric Estimation
(2009), Section 2.2.
-/

open Finset

private theorem pmf_toReal_sum {α : Type*} [Fintype α] (r : PMF α) :
    ∑ a, (r a).toReal = 1 := by
  have hne : ∀ a, r a ≠ ⊤ := by
    intro a
    have hle : r a ≤ ∑' b, r b := ENNReal.le_tsum a
    rw [PMF.tsum_coe r] at hle
    exact ne_top_of_le_ne_top ENNReal.one_ne_top hle
  have h := ENNReal.tsum_toReal_eq hne
  have hfintype : (∑' a, (r a).toReal) = ∑ a, (r a).toReal := tsum_fintype _
  rw [PMF.tsum_coe r, ENNReal.toReal_one, hfintype] at h
  exact h.symm

/-- Le Cam's two-point bound (finite form): for two distributions
`p`, `q` on a finite type and any test `δ` (deciding for `q` on
`δ a = true`), the sum of the two error probabilities is at least
`1` minus the total variation distance. Hence no test beats the
better of the two hypotheses by more than the variation allows. -/
theorem lecam_two_point {α : Type*} [Fintype α] (p q : PMF α) (δ : α → Bool) :
    1 - (1 / 2) * ∑ a, |(p a).toReal - (q a).toReal| ≤
      (∑ a ∈ Finset.univ.filter (fun a => δ a = true), (p a).toReal) +
        (∑ a ∈ Finset.univ.filter (fun a => δ a = false), (q a).toReal) := by
  have hpsum : ∑ a, (p a).toReal = 1 := pmf_toReal_sum p
  have hqsum : ∑ a, (q a).toReal = 1 := pmf_toReal_sum q
  have hmin : ∀ a : α, min (p a).toReal (q a).toReal
      = ((p a).toReal + (q a).toReal - |(p a).toReal - (q a).toReal|) / 2 := by
    intro a
    rcases le_total (p a).toReal (q a).toReal with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
      ring
  have hsum : ∑ a, min (p a).toReal (q a).toReal
      = 1 - (1 / 2) * ∑ a, |(p a).toReal - (q a).toReal| := by
    have hcongr : ∑ a, min (p a).toReal (q a).toReal
        = ∑ a, (((p a).toReal + (q a).toReal - |(p a).toReal - (q a).toReal|) / 2) :=
      Finset.sum_congr rfl (fun a _ => hmin a)
    rw [hcongr, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      hpsum, hqsum]
    ring
  have hle : ∑ a, min (p a).toReal (q a).toReal ≤
      (∑ a ∈ Finset.univ.filter (fun a => δ a = true), (p a).toReal) +
        (∑ a ∈ Finset.univ.filter (fun a => δ a = false), (q a).toReal) := by
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro a _
    cases δ a <;> simp
  rw [hsum] at hle
  exact hle
