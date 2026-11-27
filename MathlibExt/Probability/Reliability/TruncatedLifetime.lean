/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Expected truncated lifetime as a survival integral

The layer-cake formula for the minimum of an almost everywhere nonnegative function
and a finite cap gives an interval integral of the original function's strict tail measures.
-/

@[expose] public section

open Set

namespace MeasureTheory

/-- **Expected truncated lifetime as a survival integral.** Let `L` be almost everywhere
measurable and nonnegative under a finite measure `μ`. For `0 ≤ T`, the integral of
`min L T` is the interval integral `∫ t in 0..T, μ.real {ω | t < L ω}`. For a probability
measure, this is the mean of the capped lifetime. The formula includes `T = 0` and
allows atoms in the lifetime distribution. -/
theorem integral_min_eq_intervalIntegral_meas_lt {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {L : Ω → ℝ} (hL : AEMeasurable L μ)
    (hnonneg : 0 ≤ᵐ[μ] L) {T : ℝ} (hT : 0 ≤ T) :
    (∫ ω, min (L ω) T ∂μ) = ∫ t in (0 : ℝ)..T, μ.real {ω | t < L ω} := by
  have hcap : 0 ≤ᵐ[μ] (fun ω => min (L ω) T) :=
    hnonneg.mono fun _ hω => le_min hω hT
  have hi : Integrable (fun ω => min (L ω) T) μ :=
    Integrable.of_mem_Icc 0 T (hL.min aemeasurable_const)
      (hcap.mono fun _ hω => ⟨hω, min_le_right _ _⟩)
  rw [hi.integral_eq_integral_meas_lt hcap, intervalIntegral.integral_of_le hT]
  have hzero : ∀ᵐ t : ℝ, t ∈ Ioi (0 : ℝ) \ Ioc 0 T →
      μ.real {ω | t < min (L ω) T} = 0 := by
    refine Filter.Eventually.of_forall fun t ht => ?_
    have htT : ¬ t < T := fun hlt => ht.2 ⟨ht.1, hlt.le⟩
    simp [lt_min_iff, htT]
  rw [setIntegral_eq_of_subset_of_ae_sdiff_eq_zero nullMeasurableSet_Ioi Ioc_subset_Ioi_self hzero]
  apply setIntegral_congr_ae measurableSet_Ioc
  filter_upwards [(volume : Measure ℝ).ae_ne T] with t hne ht
  have htT : t < T := lt_of_le_of_ne ht.2 hne
  simp [lt_min_iff, htT]

end MeasureTheory
