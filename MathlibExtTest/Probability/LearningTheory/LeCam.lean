/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.LearningTheory.LeCam

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Tactic.NormNum

/-- Boundary check: for the two point masses `PMF.pure 0` and `PMF.pure 1` on `Fin 2`
and the test that decides `q`'s point (`δ a = decide (a = 1)`), both error probabilities
are `0` and the total variation distance is `1`, so the Le Cam bound is the equality case
`1 - 1 ≤ 0 + 0`. The computed distance and error sum pin the filter polarity and the
constants: swapping the test would make the error sum `2`, not `0`. -/
example : (0 : ℝ) ≤ 0 := by
  have hTV : MathlibExt.Probability.MarkovMixing.tvDist
      (fun a => ((PMF.pure (0 : Fin 2)) a).toReal)
      (fun a => ((PMF.pure (1 : Fin 2)) a).toReal) = 1 := by
    norm_num [MathlibExt.Probability.MarkovMixing.tvDist, Fin.sum_univ_two, PMF.pure_apply]
  have hErr : (∑ a ∈ Finset.univ.filter (fun a => decide (a = 1) = true),
        ((PMF.pure (0 : Fin 2)) a).toReal) +
      (∑ a ∈ Finset.univ.filter (fun a => decide (a = 1) = false),
        ((PMF.pure (1 : Fin 2)) a).toReal) = 0 := by
    simp [Finset.sum_filter, Fin.sum_univ_two, PMF.pure_apply]
  have h := lecam_two_point (PMF.pure (0 : Fin 2)) (PMF.pure (1 : Fin 2))
    (fun a => decide (a = 1))
  convert h using 1 <;> norm_num only [hTV, hErr]
