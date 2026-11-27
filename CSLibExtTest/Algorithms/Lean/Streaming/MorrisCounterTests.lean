/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.Streaming.MorrisCounter.Amplification

open MeasureTheory ProbabilityTheory MathlibExt.Probability.MedianOfMeans
open Cslib.Algorithms.Lean.MorrisCounter

private theorem firstToken : law 1 = Measure.dirac 1 := by
  change (Measure.dirac (0 : Fin 1)).bind (step 0) = _
  rw [Measure.dirac_bind (step 0).measurable]
  change bernoulliMeasure _ _ (incrementProb 0) = _
  rw [show incrementProb 0 = 1 from Subtype.ext (by norm_num [incrementProb]), bernoulliMeasure_one]
  rfl

-- Both outcomes at time two have positive probability, unlike the first increment.
example : (law 2).real {2} = 1 / 2 := by
  change ((law 1).bind (step 1)).real _ = _
  rw [firstToken, Measure.dirac_bind (step 1).measurable]
  convert step_increment (1 : Fin 2) using 1 <;> norm_num

example : (law 2).real {1} = 1 / 2 := by
  change ((law 1).bind (step 1)).real _ = _
  rw [firstToken, Measure.dirac_bind (step 1).measurable]
  change (bernoulliMeasure _ _ (incrementProb 1)).real _ = _
  rw [bernoulliMeasure_real_apply_of_notMem_of_mem _ (measurableSet_singleton _) (by decide) (by decide)]
  norm_num [incrementProb]

example : Var[value; law 3] = 3 := by rw [variance_value]; norm_num

-- At n = 2 a single estimator *never* has relative error at most 1/4.
example : (law 2).real {x | value x - 1 ∉ Set.Icc (3 / 2 : ℝ) (5 / 2)} = 1 := by
  have h (x : Fin 3) : value x - 1 ∉ Set.Icc (3 / 2 : ℝ) (5 / 2) := by
    fin_cases x <;> norm_num [value, Set.mem_Icc]
  simp [h]

-- Independent bounded block means achieve failure ≤ 1/4 at the very same n and precision.
example :
    (Measure.pi fun _ : Fin (groups (1/4)) => Measure.pi fun _ : Fin (width (1/4)) =>
      boundedLaw (cap (width (1/4)) 2) 2).real
        {x | sampleMedian (fun j => blockMean (x j)) ∉ Set.Icc (3/2 : ℝ) (5/2)} ≤ 1/4 := by
  convert median_failure (n := 2) (m := 2) (ε := 1/4) (δ := 1/4) le_rfl (by norm_num)
    (by norm_num) (by norm_num) using 1
  norm_num

example : ∫ x, value x - 1 ∂(law 0) = 0 := by simpa using integral_estimate 0
example : exactCounter 3 3 = 3 := by decide
example : exactCounter 3 4 = 3 := by decide

-- The first token reaches the cap; the second cannot move the bounded register beyond it.
example : boundedLaw 1 2 = Measure.dirac 1 := by
  have h : boundedLaw 1 1 = Measure.dirac 1 := by
    rw [boundedLaw, firstToken, Measure.map_dirac' (measurable_of_finite _)]
    rfl
  rw [boundedLaw_succ, h, Measure.dirac_bind (boundedStep 1).measurable]
  exact bernoulliMeasure_self_eq_dirac (1 : Fin 2) _

example : registerBits 0 = 1 := by decide
