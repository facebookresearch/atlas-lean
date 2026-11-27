/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.InformationTheory.GaussianRowMessageRefinement

open InformationTheory MeasureTheory ProbabilityTheory
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

-- The one-point refined message has finite entropy, including with an empty row array.
example {d : ℕ}
    (P : Measure ((Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 × Unit) ×
      (Fin 0 → EuclideanSpace ℝ (Fin d)))) [IsProbabilityMeasure P] :
    let P' := P.map (fun z => ((z.1.1, (z.1.2, ())), z.2))
    let γ := Measure.pi (fun _ : Fin 0 => stdGaussian (EuclideanSpace ℝ (Fin d)))
    klDiv P' (P'.fst.prod γ) = klDiv P (P.fst.prod γ) := by
  let P' := P.map (fun z => ((z.1.1, (z.1.2, ())), z.2))
  let π := P'.map (fun z => z.1.2)
  have hfinite : (∫⁻ v, ENNReal.ofReal (-Real.log (π {v}).toReal) ∂π) ≠ ∞ := by
    have hmass (v : Unit × Unit) : π {v} = 1 := by
      rw [show ({v} : Set (Unit × Unit)) = Set.univ by ext x; simp [Subsingleton.elim x v]]
      exact measure_univ
    simp [hmass]
  exact gaussianRowKL_messageRefinement P (fun _ => ()) measurable_const hfinite
