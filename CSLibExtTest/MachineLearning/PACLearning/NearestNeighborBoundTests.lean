/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.MachineLearning.PACLearning.NearestNeighborBound
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.NormNum

/-! # Tests for the finite-sample 1-nearest-neighbor bound -/

set_option autoImplicit false

namespace Cslib.MachineLearning.PACLearning

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

-- Test both label assignments, not just normalization of the kernel.
example : binaryLabelKernel (fun _ : Unit => (1 : unitInterval)) measurable_const () =
    Measure.dirac true := by
  change bernoulliMeasure true false 1 = _
  exact bernoulliMeasure_one _ _

example : binaryLabelKernel (fun _ : Unit => (0 : unitInterval)) measurable_const () =
    Measure.dirac false := by
  change bernoulliMeasure true false 0 = _
  exact bernoulliMeasure_zero _ _

private noncomputable def quarter : unitInterval := ⟨1 / 4, by constructor <;> norm_num⟩

example : (binaryLabelKernel (fun _ : Unit => quarter) measurable_const ()).real {false} =
    3 / 4 := by
  change (bernoulliMeasure true false quarter).real {false} = _
  rw [bernoulliMeasure_real_apply_of_notMem_of_mem quarter (measurableSet_singleton false)
    (by simp) (by simp)]
  norm_num [quarter]

-- A repeated feature atom makes both training distances tie, without making the labels equal.
-- With a constant posterior the bound needs no positive Lipschitz constant or density.
example (x : NearestNeighborCube 1) :
    let η := fun _ : NearestNeighborCube 1 => quarter
    let D := Measure.dirac x ⊗ₘ binaryLabelKernel η measurable_const
    (∫ S : LabeledSample (NearestNeighborCube 1) Bool 2,
      (error D (oneNearestNeighbor S)).toReal ∂Measure.pi (fun _ : Fin 2 => D)) ≤
      2 * (error D (binaryBayesClassifier η)).toReal := by
  have h : LipschitzWith 0 (fun _ : NearestNeighborCube 1 => quarter) := by
    intro a b
    simp
  simpa using integral_error_oneNearestNeighbor_le (m := 2) (Measure.dirac x) h

-- With the feature fixed and two tied training points, independent train/query labels still
-- disagree with probability `3/8`. Reusing the selected training label as the query gives zero.
example (x : NearestNeighborCube 1) :
    let η := fun _ : NearestNeighborCube 1 => quarter
    let D := Measure.dirac x ⊗ₘ binaryLabelKernel η measurable_const
    (∫ S : LabeledSample (NearestNeighborCube 1) Bool 2,
      (error D (oneNearestNeighbor S)).toReal ∂Measure.pi (fun _ : Fin 2 => D)) = 3 / 8 := by
  dsimp only
  rw [expected_error_oneNearestNeighbor_const (m := 2) (Measure.dirac x) quarter]
  norm_num [quarter]

-- For a point mass the nearest-neighbor distance is exactly zero, even with one draw.
example (x : NearestNeighborCube 1) :
    (∫ S : Fin 1 → NearestNeighborCube 1,
      ∫ y, dist y (S (nearestNeighborIndex S y)) ∂Measure.dirac x
        ∂Measure.pi (fun _ : Fin 1 => Measure.dirac x)) = 0 := by
  have h : (Measure.pi fun _ : Fin 1 => Measure.dirac x) = Measure.dirac (fun _ => x) := by
    refine Measure.pi_eq fun s hs => ?_
    rw [Fintype.prod_unique, Measure.dirac_apply' _ (MeasurableSet.univ_pi hs),
      Measure.dirac_apply' _ (hs default)]
    have hz : (fun _ : Fin 1 => x) ∈ Set.univ.pi s ↔ x ∈ s default := by
      simp only [Set.mem_univ_pi]
      exact ⟨fun hs' => hs' default, fun hs' i => (Subsingleton.elim default i) ▸ hs'⟩
    by_cases hx : x ∈ s default
    · simp only [Set.indicator_of_mem (hz.mpr hx), Set.indicator_of_mem hx, Pi.one_apply]
    · rw [Set.indicator_of_notMem (hz.not.mpr hx), Set.indicator_of_notMem hx]
  rw [h, integral_dirac, integral_dirac, dist_self]

end Cslib.MachineLearning.PACLearning
