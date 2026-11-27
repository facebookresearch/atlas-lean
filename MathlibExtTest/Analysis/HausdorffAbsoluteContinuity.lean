/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.HausdorffAbsoluteContinuity

open MeasureTheory
open MathlibExt.Analysis.HausdorffAbsoluteContinuityWanted.Analysis.HausdorffAbsoluteContinuity
open MathlibExt.Analysis.HausdorffMomentsWanted.Analysis
open scoped NNReal

-- Restricted Lebesgue probability measure on the square satisfies the moment inequalities.
example : ∃ C : ℝ, ∀ k n : Fin 2 → ℕ, k ≤ n →
    diff (momentOf (volume.restrict (cube 2))) k n ≤
      C * diff (momentOf (volume.restrict (cube 2))) k n := by
  have hcube : cube 2 = WithLp.ofLp ⁻¹' Set.Icc (0 : Fin 2 → ℝ) 1 := by
    ext x
    exact forall_and
  have hmp := PiLp.volume_preserving_ofLp (Fin 2)
  have hm : MeasurableSet (cube 2) := hcube ▸ measurableSet_Icc.preimage hmp.measurable
  have : IsProbabilityMeasure (volume.restrict (cube 2)) := by
    constructor
    rw [Measure.restrict_apply_univ, hcube, hmp.measure_preimage measurableSet_Icc.nullMeasurableSet,
      Real.volume_Icc_pi]
    simp
  refine (hausdorff_absolute_continuity _ ?_).mp ⟨1, by simp⟩
  simp [Measure.restrict_apply hm.compl]

-- No finite bound works for a point mass in positive dimension.
example : ¬ ∃ C : ℝ, ∀ k n : Fin 1 → ℕ, k ≤ n →
    diff (momentOf (Measure.dirac (0 : EuclideanSpace ℝ (Fin 1)))) k n ≤
      C * diff (momentOf (volume.restrict (cube 1))) k n := by
  intro h
  have hzero : (0 : EuclideanSpace ℝ (Fin 1)) ∈ cube 1 := fun _ => by simp
  have hs : Measure.dirac (0 : EuclideanSpace ℝ (Fin 1)) (cube 1)ᶜ = 0 := by
    simp [hzero]
  obtain ⟨c, hc⟩ := (hausdorff_absolute_continuity _ hs).mpr h
  have hle := hc ({0} : Set (EuclideanSpace ℝ (Fin 1)))
  have hnull : volume.restrict (cube 1) ({0} : Set (EuclideanSpace ℝ (Fin 1))) = 0 := by
    rw [Measure.restrict_apply (measurableSet_singleton _)]
    exact measure_mono_null Set.inter_subset_left (measure_singleton _)
  simp [smul_apply, hnull] at hle
