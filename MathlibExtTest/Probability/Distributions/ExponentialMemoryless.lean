/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Distributions.ExponentialMemoryless
import Mathlib.Tactic.NormNum

/-! # Boundary cases for the memoryless characterization -/

open MeasureTheory ProbabilityTheory Set

example : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
    (Measure.dirac (0 : ℝ)).real (Ioi (s + t)) =
      (Measure.dirac (0 : ℝ)).real (Ioi s) * (Measure.dirac (0 : ℝ)).real (Ioi t) :=
  (memoryless_iff_dirac_zero_or_expMeasure _ (by
    simp [Measure.dirac_apply' _ measurableSet_Iio])).mpr (Or.inl rfl)

example : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
    (expMeasure 2).real (Ioi (s + t)) = (expMeasure 2).real (Ioi s) *
      (expMeasure 2).real (Ioi t) := by
  have hrate : (0 : ℝ) < 2 := by norm_num
  let _ := isProbabilityMeasure_expMeasure hrate
  have hsupp : expMeasure 2 (Iio 0) = 0 := by
    refine measure_mono_null (Iio_subset_Iic_self : Iio (0 : ℝ) ⊆ Iic 0) ?_
    rw [← ofReal_cdf, cdf_expMeasure_eq hrate]
    simp
  exact (memoryless_iff_dirac_zero_or_expMeasure _ hsupp).mpr (Or.inr ⟨2, hrate, rfl⟩)

-- A strictly positive deterministic lifetime is not memoryless.
example : ¬ ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
    (Measure.dirac (1 : ℝ)).real (Ioi (s + t)) =
      (Measure.dirac (1 : ℝ)).real (Ioi s) * (Measure.dirac (1 : ℝ)).real (Ioi t) := by
  intro hm
  have h := hm (3 / 4) (3 / 4) (by norm_num) (by norm_num)
  norm_num [Measure.real, Measure.dirac_apply' _ measurableSet_Ioi, Set.indicator] at h
