/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Tactic.NormNum
public import MathlibExt.Geometry.Convex.CubeCovering

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace MetaMathlibExt

/-- The actual coordinate cube has Euclidean volume `2^n`.
This is the cube-volume identity in optimizationproblems `constants/25a.md`, line 44. -/
theorem volume_coordinateCube (n : ℕ) :
    volume (ConvexCovering.coordinateCube n) = (2 : ℝ≥0∞) ^ n := by
  rw [ConvexCovering.coordinateCube_eq_absSet]
  have hbox : {x : EuclideanSpace ℝ (Fin n) | ∀ i, |x i| ≤ 1} =
      (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm ⁻¹'
        Set.Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)) := by
    ext x
    change (∀ i, |x i| ≤ 1) ↔ (∀ i, -1 ≤ x i) ∧ (∀ i, x i ≤ 1)
    constructor
    · intro h
      exact ⟨fun i => (abs_le.mp (h i)).1, fun i => (abs_le.mp (h i)).2⟩
    · rintro ⟨hl, hu⟩ i
      exact abs_le.mpr ⟨hl i, hu i⟩
  rw [hbox, (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n)).measure_preimage
    measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi]
  norm_num [Finset.prod_const]

end MetaMathlibExt
