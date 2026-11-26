/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Process.ContinuousTimeMarkovChain.StationaryPath
import MathlibExtTest.Probability.Process.ContinuousTimeMarkovChain.Path
import MathlibExtTest.Probability.Process.ContinuousTimeMarkovChain.Stationary

open Finset Matrix ProbabilityTheory MeasureTheory
open scoped NNReal

namespace MathlibExtTest.Probability.Process.ContinuousTimeMarkovChain.StationaryPath

private theorem π2_nonneg (i : Fin 2) : 0 ≤ Stationary.π2 i := by
  fin_cases i <;> norm_num [Stationary.π2]

private theorem π2_sum : ∑ i, Stationary.π2 i = 1 := by
  norm_num [Stationary.π2, Fin.sum_univ_two]

private theorem π2_stationary : Stationary.π2 ᵥ* Path.q2 = 0 :=
  Stationary.isDetailedBalance_π2.vecMul_eq_zero Stationary.sum_row_q2

-- The nonuniform law (2/3, 1/3) is preserved even away from the initial time.
example (t : ℝ≥0) :
    (ctmcPathMeasure Path.isRateMatrix_q2 Stationary.π2).real {x | x t = 0} = 2 / 3 := by
  simpa [Stationary.π2] using
    (ctmcPathMeasure_stationary Path.isRateMatrix_q2 π2_nonneg π2_sum π2_stationary).2.1 t 0

-- A shift preserves the joint law of an observation at time zero and one at time one.
example (h : ℝ≥0) (j : Fin 2 → Fin 2) :
    (ctmcPathMeasure Path.isRateMatrix_q2 Stationary.π2).real {x | ∀ k, x (![0, 1] k + h) = j k} =
    (ctmcPathMeasure Path.isRateMatrix_q2 Stationary.π2).real {x | ∀ k, x (![0, 1] k) = j k} := by
  have ht : Monotone (![0, 1] : Fin 2 → ℝ≥0) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> norm_num at *
  exact (ctmcPathMeasure_stationary Path.isRateMatrix_q2 π2_nonneg π2_sum π2_stationary).2.2
    _ ht j h

-- Repeating an observation time is allowed, even for incompatible state requirements.
example (t h : ℝ≥0) :
    (ctmcPathMeasure Path.isRateMatrix_q2 Stationary.π2).real
        {x | ∀ k : Fin 2, x (t + h) = k} =
      (ctmcPathMeasure Path.isRateMatrix_q2 Stationary.π2).real {x | ∀ k : Fin 2, x t = k} :=
  (ctmcPathMeasure_stationary Path.isRateMatrix_q2 π2_nonneg π2_sum π2_stationary).2.2
    (fun _ : Fin 2 => t) (fun _ _ _ => le_rfl) id h

end MathlibExtTest.Probability.Process.ContinuousTimeMarkovChain.StationaryPath
