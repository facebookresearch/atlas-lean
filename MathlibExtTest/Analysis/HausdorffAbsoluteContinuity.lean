/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.HausdorffAbsoluteContinuity
import Mathlib.Tactic.NormNum

open MeasureTheory
open MathlibExt.Analysis.HausdorffAbsoluteContinuityWanted.Analysis.HausdorffAbsoluteContinuity
open MathlibExt.Analysis.HausdorffMomentsWanted.Analysis
open scoped NNReal ENNReal

private noncomputable abbrev halfInterval : Set (EuclideanSpace ℝ (Fin 1)) :=
  WithLp.ofLp ⁻¹' Set.Icc (0 : Fin 1 → ℝ) (fun _ => 1 / 2)

-- The probability measure of density 2 on [0, 1/2] is not the reference measure.
-- Check the masses of [0, 1/2] directly, then apply the forward implication.
example :
    let μ : Measure (EuclideanSpace ℝ (Fin 1)) := (2 : ℝ≥0) • volume.restrict halfInterval
    μ halfInterval = 1 ∧ volume.restrict (cube 1) halfInterval = ENNReal.ofReal (1 / 2) ∧
      ∃ C : ℝ, ∀ k n : Fin 1 → ℕ, k ≤ n →
        diff (momentOf μ) k n ≤ C * diff (momentOf (volume.restrict (cube 1))) k n := by
  intro μ
  have hmp := PiLp.volume_preserving_ofLp (Fin 1)
  have hs : MeasurableSet halfInterval := measurableSet_Icc.preimage hmp.measurable
  have hsc : halfInterval ⊆ cube 1 := by
    rw [cube_eq_preimage_Icc]
    exact Set.preimage_mono (Set.Icc_subset_Icc_right (fun _ => by norm_num))
  have hv : volume halfInterval = ENNReal.ofReal (1 / 2) := by
    rw [halfInterval, hmp.measure_preimage measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi]
    simp
  have hmass : μ Set.univ = 1 := by
    simp only [μ, smul_apply, Measure.restrict_apply_univ, hv]
    change (2 : ℝ≥0∞) * ENNReal.ofReal (1 / 2) = 1
    rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have : IsProbabilityMeasure μ := ⟨hmass⟩
  have hμs : μ halfInterval = 1 := by
    simpa [μ, smul_apply, Measure.restrict_apply hs] using hmass
  have hmassRef : volume.restrict (cube 1) halfInterval = ENNReal.ofReal (1 / 2) := by
    rwa [Measure.restrict_apply hs, Set.inter_eq_left.mpr hsc]
  have hsupport : μ (cube 1)ᶜ = 0 := by
    rw [show μ = (2 : ℝ≥0) • volume.restrict halfInterval from rfl, smul_apply,
      Measure.restrict_apply isCompact_cube.measurableSet.compl,
      Set.disjoint_iff_inter_eq_empty.mp (Set.disjoint_compl_left_iff_subset.mpr hsc), measure_empty,
      smul_zero]
  have hdom : μ ≤ (2 : ℝ≥0) • volume.restrict (cube 1) := by
    intro t
    simp only [μ, smul_apply]
    exact smul_le_smul_of_nonneg_left (Measure.restrict_mono_set volume hsc t) (by norm_num)
  exact ⟨hμs, hmassRef, (hausdorff_absolute_continuity μ hsupport).mp
    (uniformlyAbsolutelyContinuous_iff.mpr ⟨2, hdom⟩)⟩

-- No finite bound works for a point mass in positive dimension.
example : ¬ ∃ C : ℝ, ∀ k n : Fin 1 → ℕ, k ≤ n →
    diff (momentOf (Measure.dirac (0 : EuclideanSpace ℝ (Fin 1)))) k n ≤
      C * diff (momentOf (volume.restrict (cube 1))) k n := by
  intro h
  have hzero : (0 : EuclideanSpace ℝ (Fin 1)) ∈ cube 1 := by
    rw [cube_eq_preimage_Icc]
    simp
  have hs : Measure.dirac (0 : EuclideanSpace ℝ (Fin 1)) (cube 1)ᶜ = 0 := by
    simp [hzero]
  obtain ⟨c, hc⟩ := uniformlyAbsolutelyContinuous_iff.mp
    ((hausdorff_absolute_continuity _ hs).mpr h)
  have hle := hc ({0} : Set (EuclideanSpace ℝ (Fin 1)))
  have hnull : volume.restrict (cube 1) ({0} : Set (EuclideanSpace ℝ (Fin 1))) = 0 := by
    rw [Measure.restrict_apply (measurableSet_singleton _)]
    exact measure_mono_null Set.inter_subset_left (measure_singleton _)
  simp [smul_apply, hnull] at hle
