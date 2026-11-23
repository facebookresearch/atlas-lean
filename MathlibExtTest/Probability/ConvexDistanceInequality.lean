/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ConvexDistanceInequality
public import Mathlib.MeasureTheory.Constructions.UnitInterval

/-!
# Tests for Talagrand's convex-distance inequality

The inequality and its tail form for the uniform probability on the unit interval, which has no
atoms, so that the finite-alphabet version does not apply: for every measurable set, for the
whole cube, for the empty set (where the right-hand side is `∞`), in dimension `0`, and for the
half-cube `{x | x₀ ≤ 1/2}` of probability `1/2`; and the monotonicity of the convex distance in
the set.
-/

@[expose] public section

namespace MathlibExtTest.Probability.ConvexDistanceInequality

open MeasureTheory MathlibExt.Probability.ConvexDistance
  MathlibExt.Probability.ConvexDistanceWanted
open scoped ENNReal unitInterval

/-- The inequality for the uniform probability on `[0, 1]` and any measurable `A ⊆ [0, 1]^N`. -/
example (N : ℕ) {A : Set (Fin N → I)} (hA : MeasurableSet A) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (convexDistance A x ^ 2 / 4)) ∂Measure.pi (fun _ => volume) ≤
      (Measure.pi (fun _ => (volume : Measure I)) A)⁻¹ :=
  lintegral_exp_convexDistance_sq_le volume N hA

/-- The upper-integral form for the same measure: a measurable majorant. -/
example (N : ℕ) {A : Set (Fin N → I)} (hA : MeasurableSet A) :
    ∃ G : (Fin N → I) → ℝ≥0∞, Measurable G ∧
      (∀ x, ENNReal.ofReal (Real.exp (convexDistance A x ^ 2 / 4)) ≤ G x) ∧
      (∫⁻ x, G x ∂Measure.pi (fun _ => volume)) * Measure.pi (fun _ => (volume : Measure I)) A ≤
        1 :=
  exists_measurable_ge_exp_convexDistance_sq volume N hA

/-- For the whole cube, the bound is `1`. -/
example (N : ℕ) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (convexDistance (Set.univ : Set (Fin N → I)) x ^ 2 / 4))
      ∂Measure.pi (fun _ => volume) ≤ 1 := by
  simpa using lintegral_exp_convexDistance_sq_le (volume : Measure I) N MeasurableSet.univ

/-- For the empty set, `P(A) = 0` and the bound of the tail form is `∞`. -/
example (N : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Measure.pi (fun _ => (volume : Measure I)) {x | t ≤ convexDistance (∅ : Set (Fin N → I)) x} ≤
      ∞ := by
  have h := measure_le_convexDistance_le (volume : Measure I) N MeasurableSet.empty ht
  rwa [measure_empty, ENNReal.inv_zero,
    ENNReal.mul_top (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'] at h

/-- The convex distance to the whole cube is at most the convex distance to its subset
`{x | x₀ ≤ 0}`. -/
example (N : ℕ) (x : Fin (N + 1) → I) :
    convexDistance Set.univ x ≤ convexDistance (Function.eval 0 ⁻¹' Set.Iic (0 : I)) x :=
  convexDistance_le_convexDistance_of_subset (Set.subset_univ _) ⟨fun _ => 0, le_rfl⟩ x

/-- In dimension `0`, the inequality for a nonempty set says `1 ≤ 1`. -/
example :
    ∫⁻ x, ENNReal.ofReal (Real.exp (convexDistance (Set.univ : Set (Fin 0 → I)) x ^ 2 / 4))
      ∂Measure.pi (fun _ => volume) ≤ 1 := by
  simpa using lintegral_exp_convexDistance_sq_le (volume : Measure I) 0 MeasurableSet.univ

/-- The points of `[0, 1]^{N+1}` whose first coordinate is at most `1 / 2`. -/
noncomputable def lowerHalf (N : ℕ) : Set (Fin (N + 1) → I) :=
  Function.eval 0 ⁻¹' Set.Iic ⟨1 / 2, by norm_num, by norm_num⟩

theorem measurableSet_lowerHalf (N : ℕ) : MeasurableSet (lowerHalf N) :=
  measurableSet_Iic.preimage (measurable_pi_apply 0)

theorem pi_lowerHalf (N : ℕ) : Measure.pi (fun _ => (volume : Measure I)) (lowerHalf N) = 2⁻¹ := by
  rw [lowerHalf, (measurePreserving_eval (fun _ => (volume : Measure I)) 0).measure_preimage
    measurableSet_Iic.nullMeasurableSet, unitInterval.volume_Iic]
  rw [show ((⟨1 / 2, by norm_num, by norm_num⟩ : I) : ℝ) = 2⁻¹ by norm_num,
    ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]

/-- For the half-cube, `∫ exp(f_c² / 4) dP ≤ 2`. -/
example (N : ℕ) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (convexDistance (lowerHalf N) x ^ 2 / 4))
      ∂Measure.pi (fun _ => volume) ≤ 2 := by
  simpa [pi_lowerHalf] using
    lintegral_exp_convexDistance_sq_le (volume : Measure I) (N + 1) (measurableSet_lowerHalf N)

/-- For the half-cube, `P(f_c ≥ 2) ≤ 2 e^{-1}`. -/
example (N : ℕ) :
    Measure.pi (fun _ => (volume : Measure I)) {x | 2 ≤ convexDistance (lowerHalf N) x} ≤
      ENNReal.ofReal (Real.exp (-1)) * 2 := by
  have h := measure_le_convexDistance_le (volume : Measure I) (N + 1) (measurableSet_lowerHalf N)
    (t := 2) (by norm_num)
  rw [pi_lowerHalf, inv_inv] at h
  convert h using 4
  norm_num

end MathlibExtTest.Probability.ConvexDistanceInequality
