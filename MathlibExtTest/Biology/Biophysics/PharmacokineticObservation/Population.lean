/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Biophysics.PharmacokineticObservation.Population

/-! Tests: singleton visit law and zero variance. -/

namespace MathlibExtTest.Biology.Biophysics.PharmacokineticObservation.Population

open MathlibExt.Biology.Biophysics.PharmacokineticObservation.Population
open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- One visit, `m = 0`, `v = 1`. -/
example : (Measure.pi (fun j : Fin 1 => gaussianReal (0 : ℝ) 1)).map
    (fun e : Fin 1 → ℝ => fun j => Real.exp ((0 : Fin 1 → ℝ) j + e j)) =
    Measure.pi (fun j : Fin 1 => (gaussianReal ((0 : Fin 1 → ℝ) j) 1).map Real.exp) :=
  visit_law_fixed_latent 0 1

/-- Zero variance `v = 0` is valid (Dirac boundary). -/
example : (Measure.pi (fun j : Fin 1 => gaussianReal (0 : ℝ) 0)).map
    (fun e : Fin 1 → ℝ => fun j => Real.exp ((0 : Fin 1 → ℝ) j + e j)) =
    Measure.pi (fun j : Fin 1 => (gaussianReal ((0 : Fin 1 → ℝ) j) 0).map Real.exp) :=
  visit_law_fixed_latent 0 0

/-- Zero-variance rate at `muV = 0`, `muCL = 1` is `exp 1`. -/
example : Real.exp (1 - 0 : ℝ) = Real.exp 1 ∧
    Real.exp (1 : ℝ) / Real.exp (0 : ℝ) = Real.exp (1 - 0) := by
  have h := pop_zero_rate (muV := (0:ℝ)) (muCL := (1:ℝ))
  exact ⟨by norm_num, h.2⟩

/-- Zero-variance collapse at the means `(0, 1)`. -/
example :
    ((ProbabilityTheory.gaussianReal (0:ℝ) 0).prod
      (ProbabilityTheory.gaussianReal (1:ℝ) 0)).map
        (fun p : ℝ × ℝ => (Real.exp p.1, Real.exp p.2)) =
      MeasureTheory.Measure.dirac (Real.exp 0, Real.exp 1) :=
  pop_zero_law_agreement

/-- Shared intercept cancels in a within-subject difference. -/
example : ((3:ℝ) + 2 + 1) - (1 + 2 + 4) = (3 + 1) - (1 + 4) :=
  intercept_cancels_within_subject

/-- Shared intercept appears as the common factor `exp b`. -/
example : Real.exp (3 + 2 + 1 : ℝ) = Real.exp 2 * Real.exp (3 + 1) :=
  intercept_exp_factor

end MathlibExtTest.Biology.Biophysics.PharmacokineticObservation.Population
