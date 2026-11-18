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
unbiasedness on a constant family (every observation is the
constant `2` on a one-point space), through the public theorem.

These are elaboration and non-vacuity checks, not new results.
-/

open SpatialPredictor ProbabilityTheory

/-- Constant family on : predictor mean equals target mean. -/
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

/-- Nonconstant one-observation family on `Bool`: positive
semidefiniteness and the error-variance identity, through the
public theorems. -/
example : (covMatrix (MeasureTheory.Measure.dirac false)
      (fun _ : Fin 1 => fun ω : Bool => if ω then (1 : ℝ) else 0)).PosSemidef
    ∧ ProbabilityTheory.variance
        (fun ω : Bool => (if ω then (1 : ℝ) else 0)
          - ∑ i : Fin 1, (fun _ : Fin 1 => (1 : ℝ)) i
            * (fun _ : Fin 1 => fun ω : Bool => if ω then (1 : ℝ) else 0) i ω)
        (MeasureTheory.Measure.dirac false)
      = ProbabilityTheory.variance (fun ω : Bool => if ω then (1 : ℝ) else 0)
          (MeasureTheory.Measure.dirac false)
        - 2 * dotProduct (fun _ : Fin 1 => (1 : ℝ))
            (covVector (MeasureTheory.Measure.dirac false)
              (fun ω : Bool => if ω then (1 : ℝ) else 0)
              (fun _ : Fin 1 => fun ω : Bool => if ω then (1 : ℝ) else 0))
        + dotProduct (fun _ : Fin 1 => (1 : ℝ))
            (Matrix.mulVec
              (covMatrix (MeasureTheory.Measure.dirac false)
                (fun _ : Fin 1 => fun ω : Bool => if ω then (1 : ℝ) else 0))
              (fun _ : Fin 1 => (1 : ℝ))) := by
  have hLp : ∀ i : Fin 1, MeasureTheory.MemLp
      ((fun _ : Fin 1 => fun ω : Bool => if ω then (1 : ℝ) else 0) i) 2
      (MeasureTheory.Measure.dirac false) := by
    intro i
    apply MeasureTheory.MemLp.of_bound (μ :=
      MeasureTheory.Measure.dirac false) (by fun_prop) 1
    exact Filter.Eventually.of_forall (fun ω => by cases ω <;> simp)
  refine ⟨covMatrix_posSemidef _ _ hLp, ?_⟩
  exact (predictor_unbiased_and_error_variance
    (MeasureTheory.Measure.dirac false)
    (X := fun ω : Bool => if ω then (1 : ℝ) else 0)
    (Y := fun _ : Fin 1 => fun ω : Bool => if ω then (1 : ℝ) else 0)
    (w := fun _ : Fin 1 => (1 : ℝ)) (hLp 0) hLp
    (fun i => by fin_cases i; rfl) (by simp)).2
