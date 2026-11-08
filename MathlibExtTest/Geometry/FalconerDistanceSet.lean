/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Characterizations of actual Euclidean distance sets and the planar threshold

Local Codex tests by `/root/finish_c32_saved`; the source model is adapted from
the canonical FalconerDistanceSet entry and the retained C34a catalogue work.
-/
module

import MathlibExt.Geometry.FalconerDistanceSet
import Mathlib.Tactic.NormNum

@[expose] public section

open MeasureTheory
open scoped ENNReal
open FalconerDistanceSet

namespace MathlibExtTest.FalconerDistanceSet

example : distanceSet (∅ : Set (EuclideanSpace ℝ (Fin 2))) = ∅ :=
  distanceSet_empty 2

example : distanceSet ({0} : Set (EuclideanSpace ℝ (Fin 2))) = {0} :=
  distanceSet_singleton 0

example : volume (distanceSet ({0} : Set (EuclideanSpace ℝ (Fin 2)))) = 0 := by
  rw [distanceSet_singleton]
  simp

example : admissiblePlanarThreshold 2 := two_admissiblePlanarThreshold

example : {s | admissiblePlanarThreshold s}.Nonempty :=
  admissiblePlanarThresholds_nonempty

example : (0 : ℝ≥0∞) ≤ planarDistanceThreshold := trivialLowerBound

example : planarDistanceThreshold ≤ 2 := planarDistanceThreshold_le_two

example : planarDistanceThreshold ≠ ⊤ := planarDistanceThreshold_ne_top

example : ENNReal.ofReal planarDistanceThreshold.toReal = planarDistanceThreshold :=
  planarDistanceThreshold_ofReal_toReal

example : ¬ admissiblePlanarThreshold (3 : ℝ≥0∞) := by
  intro h
  have := h.1.2
  norm_num at this

example : ¬ admissiblePlanarThreshold (⊤ : ℝ≥0∞) := by
  intro h
  have := h.1.2
  norm_num at this

example : planarThresholdProperty planarDistanceThreshold :=
  planarThresholdProperty_planarDistanceThreshold

example : IsLeast {s | admissiblePlanarThreshold s} planarDistanceThreshold :=
  isLeast_admissiblePlanarThresholds

example : planarDistanceThreshold.toReal =
    sInf {r : ℝ | r ∈ Set.Icc 0 2 ∧ planarThresholdProperty (ENNReal.ofReal r)} :=
  planarDistanceThreshold_toReal_eq_real_sInf

example : admissiblePlanarThreshold (ENNReal.ofReal (1 : ℝ)) ↔
    (1 : ℝ) ∈ Set.Icc 0 2 ∧ planarThresholdProperty (ENNReal.ofReal (1 : ℝ)) :=
  ofReal_admissiblePlanarThreshold_iff (by norm_num)

example : (0 : ℝ) ≤ planarDistanceThreshold.toReal := ENNReal.toReal_nonneg

example : planarDistanceThreshold.toReal ≤ (2 : ℝ) := by
  have h := (ENNReal.toReal_le_toReal planarDistanceThreshold_ne_top
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).mpr planarDistanceThreshold_le_two
  simpa using h

private theorem unitBall_axisInterval : Set.Icc (0 : ℝ) 1 ⊆
    distanceSet (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
  intro r hr
  refine ⟨0, by simp, PiLp.single 2 (0 : Fin 2) r, ?_, ?_⟩
  · simpa [Metric.mem_closedBall, dist_zero_right, PiLp.norm_single,
      Real.norm_eq_abs, abs_of_nonneg hr.1] using hr.2
  · simp [dist_zero_left, PiLp.norm_single, Real.norm_eq_abs, abs_of_nonneg hr.1]

example : IsCompact (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
  isCompact_closedBall _ _

example : dimH (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) = 2 := by
  simpa using Real.dimH_of_mem_nhds
    (Metric.closedBall_mem_nhds (0 : EuclideanSpace ℝ (Fin 2)) (by norm_num))

example : Set.Icc (0 : ℝ) 1 ⊆
    distanceSet (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) := unitBall_axisInterval

example : 1 ≤ volume (distanceSet (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)) := by
  calc
    1 = volume (Set.Icc (0 : ℝ) 1) := by simp
    _ ≤ _ := measure_mono unitBall_axisInterval

example : 0 < volume (distanceSet (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)) := by
  have h : volume (Set.Icc (0 : ℝ) 1) ≤
      volume (distanceSet (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)) :=
    measure_mono unitBall_axisInterval
  have hI : volume (Set.Icc (0 : ℝ) 1) = 1 := by simp
  rw [hI] at h
  exact lt_of_lt_of_le (by norm_num) h

example : (3 : ℝ≥0∞) / 2 < dimH (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
  rw [Real.dimH_of_mem_nhds
    (Metric.closedBall_mem_nhds (0 : EuclideanSpace ℝ (Fin 2)) (by norm_num))]
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat]
  rw [ENNReal.div_lt_iff (by norm_num) (by norm_num)]
  norm_num

example : (4 : ℝ≥0∞) / 3 < dimH (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
  rw [Real.dimH_of_mem_nhds
    (Metric.closedBall_mem_nhds (0 : EuclideanSpace ℝ (Fin 2)) (by norm_num))]
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat]
  rw [ENNReal.div_lt_iff (by norm_num) (by norm_num)]
  norm_num

example : (5 : ℝ≥0∞) / 4 < dimH (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
  rw [Real.dimH_of_mem_nhds
    (Metric.closedBall_mem_nhds (0 : EuclideanSpace ℝ (Fin 2)) (by norm_num))]
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat]
  rw [ENNReal.div_lt_iff (by norm_num) (by norm_num)]
  norm_num

example : dist (WithLp.toLp 2 ![(1 : ℝ), 1] : EuclideanSpace ℝ (Fin 2)) 0 ^ 2 = 2 := by
  rw [EuclideanSpace.dist_sq_eq]
  norm_num [Fin.sum_univ_two]

example : (0 : ℝ≥0∞) ≤ planarDistanceThreshold := by
  apply le_planarDistanceThreshold_of_zeroMeasureWitness (E := {0})
  · exact isCompact_singleton
  · rw [dimH_singleton]
  · rw [distanceSet_singleton]
    simp

example (h : planarThresholdProperty ((5 : ℝ≥0∞) / 4)) :
    planarDistanceThreshold ≤ (5 : ℝ≥0∞) / 4 :=
  planarDistanceThreshold_le_of_property
    ((ENNReal.div_le_iff (by norm_num) (by norm_num)).mpr (by norm_num)) h

#eval "C34_MODEL_CHARACTERIZATION_PROOF_ELABORATED examples=28 actual_set=unit_closed_ball"

end MathlibExtTest.FalconerDistanceSet
