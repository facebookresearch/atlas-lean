/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import MathlibExt.Probability.SpatialPredictor

/-!
# Spatial-predictor checks

Focused checks for `MathlibExt.Probability.SpatialPredictor`:
unbiasedness on a constant family, positive semidefiniteness via
the existing covariance theorem, and a nondegenerate two-point
example where the prediction-error variance is `1`, independently
of the covariance formula.

These are elaboration and non-vacuity checks, not new results.
-/

open SpatialPredictor ProbabilityTheory
open scoped ENNReal

/-- The two-point probability law on `Bool`. -/
noncomputable def twoPoint : MeasureTheory.Measure Bool :=
  (2 : ℝ≥0∞)⁻¹ • MeasureTheory.Measure.dirac true
    + (2 : ℝ≥0∞)⁻¹ • MeasureTheory.Measure.dirac false

instance : MeasureTheory.IsProbabilityMeasure twoPoint := by
  refine ⟨?_⟩
  simp [twoPoint, MeasureTheory.Measure.add_apply,
    MeasureTheory.Measure.smul_apply, ENNReal.inv_two_add_inv_two]

/-- Constant family on `Unit`: predictor mean equals target mean. -/
example : ∫ _ω : Unit, (∑ i : Fin 1, (fun _ : Fin 1 => (1 : ℝ)) i
      * (fun _ : Fin 1 => fun _ : Unit => (2 : ℝ)) i _ω)
      ∂(MeasureTheory.Measure.dirac ())
    = ∫ _ω : Unit, (2 : ℝ) ∂(MeasureTheory.Measure.dirac ()) := by
  have hX : MeasureTheory.MemLp (fun _ : Unit => (2 : ℝ)) 2
      (MeasureTheory.Measure.dirac ()) :=
    MeasureTheory.MemLp.of_bound (by fun_prop) (2 : ℝ) (by simp)
  have h := (predictor_unbiased_and_error_variance
    (MeasureTheory.Measure.dirac () : MeasureTheory.Measure Unit)
    (X := fun _ : Unit => (2 : ℝ))
    (Y := fun _ : Fin 1 => fun _ : Unit => (2 : ℝ))
    (w := fun _ : Fin 1 => (1 : ℝ)) hX (fun _ => hX) (fun _ => rfl)
    (by simp)).1
  simpa using h

/-- Nondegenerate example: target is the indicator of `true`, the
sole observation is the indicator of `false`, both with mean `1/2`
under `twoPoint`. The covariance matrix is positive semidefinite
(existing theorem), and the error-variance identity holds through
the public theorem. -/
example : (MathlibExt.Probability.Finance.PortfolioVariance.covMatrix twoPoint
      (fun _ : Fin 1 => fun ω : Bool => if ω then (0 : ℝ) else 1)).PosSemidef
    ∧ ProbabilityTheory.variance
        (fun ω : Bool => (if ω then (1 : ℝ) else 0)
          - ∑ i : Fin 1, (fun _ : Fin 1 => (1 : ℝ)) i
            * (fun _ : Fin 1 => fun ω : Bool => if ω then (0 : ℝ) else 1) i ω)
        twoPoint
      = ProbabilityTheory.variance (fun ω : Bool => if ω then (1 : ℝ) else 0)
          twoPoint
        - 2 * dotProduct (fun _ : Fin 1 => (1 : ℝ))
            (covVector twoPoint (fun ω : Bool => if ω then (1 : ℝ) else 0)
              (fun _ : Fin 1 => fun ω : Bool => if ω then (0 : ℝ) else 1))
        + dotProduct (fun _ : Fin 1 => (1 : ℝ))
            (Matrix.mulVec
              (MathlibExt.Probability.Finance.PortfolioVariance.covMatrix twoPoint
                (fun _ : Fin 1 => fun ω : Bool => if ω then (0 : ℝ) else 1))
              (fun _ : Fin 1 => (1 : ℝ))) := by
  have hLp : ∀ i : Fin 1, MeasureTheory.MemLp
      ((fun _ : Fin 1 => fun ω : Bool => if ω then (0 : ℝ) else 1) i) 2
      twoPoint := by
    intro i
    apply MeasureTheory.MemLp.of_bound (μ := twoPoint) (by fun_prop) 1
    exact Filter.Eventually.of_forall (fun ω => by cases ω <;> simp)
  have hX : MeasureTheory.MemLp (fun ω : Bool => if ω then (1 : ℝ) else 0) 2
      twoPoint :=
    MeasureTheory.MemLp.of_bound (by fun_prop) 1
      (Filter.Eventually.of_forall (fun ω => by cases ω <;> simp))
  refine ⟨ProbabilityTheory.posSemidef_covariance_matrix hLp, ?_⟩
  exact (predictor_unbiased_and_error_variance twoPoint
    (X := fun ω : Bool => if ω then (1 : ℝ) else 0)
    (Y := fun _ : Fin 1 => fun ω : Bool => if ω then (0 : ℝ) else 1)
    (w := fun _ : Fin 1 => (1 : ℝ)) hX hLp
    (fun i => by
      fin_cases i
      show ∫ x : Bool, (if x then (0 : ℝ) else 1)
          ∂((2 : ℝ≥0∞)⁻¹ • MeasureTheory.Measure.dirac true
            + (2 : ℝ≥0∞)⁻¹ • MeasureTheory.Measure.dirac false)
        = ∫ x : Bool, (if x then (1 : ℝ) else 0)
          ∂((2 : ℝ≥0∞)⁻¹ • MeasureTheory.Measure.dirac true
            + (2 : ℝ≥0∞)⁻¹ • MeasureTheory.Measure.dirac false)
      haveI : MeasureTheory.IsFiniteMeasure
          ((2 : ℝ≥0∞)⁻¹ • MeasureTheory.Measure.dirac true) := ⟨by simp⟩
      haveI : MeasureTheory.IsFiniteMeasure
          ((2 : ℝ≥0∞)⁻¹ • MeasureTheory.Measure.dirac false) := ⟨by simp⟩
      rw [MeasureTheory.integral_add_measure
          MeasureTheory.Integrable.of_finite
          MeasureTheory.Integrable.of_finite,
        MeasureTheory.integral_smul_measure,
        MeasureTheory.integral_smul_measure,
        MeasureTheory.integral_dirac, MeasureTheory.integral_dirac]
      rw [MeasureTheory.integral_add_measure
          MeasureTheory.Integrable.of_finite
          MeasureTheory.Integrable.of_finite,
        MeasureTheory.integral_smul_measure,
        MeasureTheory.integral_smul_measure,
        MeasureTheory.integral_dirac, MeasureTheory.integral_dirac]
      norm_num) (by simp)).2

/-- Independent numeric check: for the two-point family above, the
prediction error `X - Y 0` takes values `1` and `-1` with equal
probability, so its variance is `1`. Proved by evaluating the
integrals over `twoPoint` directly, without the predictor theorem. -/
example : ProbabilityTheory.variance
    (fun ω : Bool => (if ω then (1 : ℝ) else 0)
      - (if ω then (0 : ℝ) else 1)) twoPoint = 1 := by
  have hmean : ∫ ω : Bool, ((if ω then (1 : ℝ) else 0)
        - (if ω then (0 : ℝ) else 1)) ∂twoPoint = 0 := by
    show ∫ ω : Bool, ((if ω then (1 : ℝ) else 0)
        - (if ω then (0 : ℝ) else 1))
        ∂((2 : ℝ≥0∞)⁻¹ • MeasureTheory.Measure.dirac true
          + (2 : ℝ≥0∞)⁻¹ • MeasureTheory.Measure.dirac false) = 0
    haveI : MeasureTheory.IsFiniteMeasure
        ((2 : ℝ≥0∞)⁻¹ • MeasureTheory.Measure.dirac true) := ⟨by simp⟩
    haveI : MeasureTheory.IsFiniteMeasure
        ((2 : ℝ≥0∞)⁻¹ • MeasureTheory.Measure.dirac false) := ⟨by simp⟩
    rw [MeasureTheory.integral_add_measure
        MeasureTheory.Integrable.of_finite
        MeasureTheory.Integrable.of_finite,
      MeasureTheory.integral_smul_measure,
      MeasureTheory.integral_smul_measure,
      MeasureTheory.integral_dirac, MeasureTheory.integral_dirac]
    norm_num
  rw [ProbabilityTheory.variance, ProbabilityTheory.evariance, hmean]
  show (∫⁻ ω : Bool, ‖(if ω then (1 : ℝ) else 0)
        - (if ω then (0 : ℝ) else 1) - 0‖ₑ ^ 2
      ∂((2 : ℝ≥0∞)⁻¹ • MeasureTheory.Measure.dirac true
        + (2 : ℝ≥0∞)⁻¹ • MeasureTheory.Measure.dirac false)).toReal = 1
  rw [MeasureTheory.lintegral_add_measure,
    MeasureTheory.lintegral_smul_measure,
    MeasureTheory.lintegral_smul_measure,
    MeasureTheory.lintegral_dirac, MeasureTheory.lintegral_dirac]
  simp
  rw [ENNReal.inv_two_add_inv_two, ENNReal.toReal_one]
