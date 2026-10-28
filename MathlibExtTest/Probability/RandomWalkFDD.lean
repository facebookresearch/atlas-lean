/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import MathlibExt.Probability.RandomWalkFDD

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

-- The hypotheses discharge for the partition `0 < 1 < 3`, with limiting variances `1` and `2`.
example {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {R : ℕ → Ω → ℝ} (hR_meas : ∀ i, Measurable (R i)) (hR_mean : ∀ i, ∫ ω, R i ω ∂P = 0)
    (hR_var : ∀ i, ∫ ω, R i ω ^ 2 ∂P = 1) (hR_bdd : ∀ i ω, |R i ω| ≤ 1)
    (hindep : iIndepFun R P) (hident : ∀ i, IdentDistrib (R i) (R 0) P P)
    {Z : Fin 2 → Ω' → ℝ} (hZ0 : HasLaw (Z 0) (gaussianReal 0 1) P')
    (hZ1 : HasLaw (Z 1) (gaussianReal 0 2) P') (hZindep : iIndepFun Z P') : True := by
  have ht : StrictMono ![(0 : ℝ), 1, 3] := by
    refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
    fin_cases i <;> norm_num
  have := tendstoInDistribution_randomWalk_increments hR_meas hR_mean hR_var hR_bdd hindep hident
    _ ht (by norm_num) (Fin.forall_fin_two.2
      ⟨by convert hZ0 using 3; norm_num, by convert hZ1 using 3; norm_num⟩) hZindep
  trivial

#print axioms tendstoInDistribution_randomWalk_increments
