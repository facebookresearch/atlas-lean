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

end MathlibExtTest.Biology.Biophysics.PharmacokineticObservation.Population
