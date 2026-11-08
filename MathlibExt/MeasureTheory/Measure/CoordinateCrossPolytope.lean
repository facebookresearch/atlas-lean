/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FunProp

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace MetaMathlibExt

private theorem volume_piCoordinateCrossPolytope (n : ℕ) (hn : 0 < n) :
    volume {x : Fin n → ℝ | ∑ i, |x i| ≤ 1} =
      (2 : ℝ≥0∞) ^ n / (n.factorial : ℝ≥0∞) := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hgamma : Real.Gamma (2 : ℝ) = 1 := by
    simp
  have h := MeasureTheory.volume_sum_rpow_le (Fin n) (p := 1) (by norm_num) 1
  norm_num [Real.Gamma_nat_eq_factorial, hgamma] at h
  rw [h, ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num)]
  norm_num

/-- The actual coordinate cross-polytope has Euclidean volume `2^n/n!`.
This is the polar-volume identity in optimizationproblems `constants/25a.md`, line 44. -/
theorem volume_coordinateCrossPolytope (n : ℕ) (hn : 0 < n) :
    volume {x : EuclideanSpace ℝ (Fin n) | ∑ i, |x i| ≤ 1} =
      (2 : ℝ≥0∞) ^ n / (n.factorial : ℝ≥0∞) := by
  have hset : {x : EuclideanSpace ℝ (Fin n) | ∑ i, |x i| ≤ 1} =
      (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm ⁻¹'
        {x : Fin n → ℝ | ∑ i, |x i| ≤ 1} := rfl
  have hs : MeasurableSet {x : Fin n → ℝ | ∑ i, |x i| ≤ 1} :=
    measurableSet_le (by fun_prop) (by fun_prop)
  rw [hset, (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n)).measure_preimage
    hs.nullMeasurableSet, volume_piCoordinateCrossPolytope n hn]

end MetaMathlibExt
