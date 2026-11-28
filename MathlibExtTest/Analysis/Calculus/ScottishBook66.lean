/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Calculus.ScottishBook66
import Mathlib.MeasureTheory.Measure.Prod

/-! # Scottish Book Problem 66 regression -/

open MathlibExt.Analysis.Calculus.ScottishBook66Wanted MeasureTheory Set

-- The product-order interval and the open square differ only on null coordinate lines.
private theorem volume_restrict_legacy_eq :
    volume.restrict (Ioo (0, 0) (1, 1) : Set (ℝ × ℝ)) =
      volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
  apply Measure.restrict_congr_set
  rw [Measure.volume_eq_prod ℝ ℝ]
  apply Filter.eventuallyEqSet_iff.2
  have h0 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 0 := by simp [ae_iff]
  have h1 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 1 := by simp [ae_iff]
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (h0.and h1),
    Measure.quasiMeasurePreserving_snd.ae (h0.and h1)] with p hx hy
  constructor
  · rintro ⟨hlo, hhi⟩
    exact ⟨⟨lt_of_le_of_ne hlo.le.1 hx.1.symm, lt_of_le_of_ne hhi.le.1 hx.2⟩,
      ⟨lt_of_le_of_ne hlo.le.2 hy.1.symm, lt_of_le_of_ne hhi.le.2 hy.2⟩⟩
  · rintro ⟨hpx, hpy⟩
    exact ⟨lt_of_le_not_ge ⟨hpx.1.le, hpy.1.le⟩ (fun h ↦ hpx.1.not_ge h.1),
      lt_of_le_not_ge ⟨hpx.2.le, hpy.2.le⟩ (fun h ↦ hpx.2.not_ge h.1)⟩

-- Unpack the refutation into a counterexample for the specified derivative order and measure.
example : ∃ f : ℝ × ℝ → ℝ,
    (∀ x y : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 → y ∈ Set.Ioo (0 : ℝ) 1 →
      DifferentiableAt ℝ (fun t ↦ f (t, y)) x) ∧
    (∀ x y : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 → y ∈ Set.Ioo (0 : ℝ) 1 →
      DifferentiableAt ℝ (fun t ↦ f (x, t)) y) ∧
    (∀ x y : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 → y ∈ Set.Ioo (0 : ℝ) 1 →
      DifferentiableAt ℝ (deriv (fun t ↦ f (t, y))) x) ∧
    (∀ x y : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 → y ∈ Set.Ioo (0 : ℝ) 1 →
      DifferentiableAt ℝ (deriv (fun t ↦ f (x, t))) y) ∧
    0 < (volume.restrict (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1))
      {p | ¬ DifferentiableAt ℝ (fun t ↦ deriv (fun s ↦ f (t, s)) p.2) p.1} := by
  classical
  rw [← volume_restrict_legacy_eq]
  have h := mazur66_refuted
  simp only [ScottishBookProblem66Claim, not_forall, ae_iff] at h
  obtain ⟨f, hx, hy, hxx, hyy, hfail⟩ := h
  exact ⟨f, hx, hy, hxx, hyy, pos_iff_ne_zero.mpr hfail⟩
