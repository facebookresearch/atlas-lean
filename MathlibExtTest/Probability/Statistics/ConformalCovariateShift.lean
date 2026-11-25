/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.ConformalCovariateShift
import Mathlib.Probability.UniformOn
import Mathlib.Tactic.NormNum

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.Statistics.WeightedConformal
open MathlibExt.Probability.ConformalCovariateShiftWanted
open scoped ENNReal

namespace MathlibExtTest.Probability.Statistics.ConformalCovariateShift

/-- With no calibration observations the threshold is infinite and coverage is one. -/
example {X : Type*} [MeasurableSpace X] (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (s : X → ℝ) (β : ℝ) (w : X → ℝ) :
    ((Measure.pi fun _ : Fin 0 => μ).prod ν)
      {D | (s D.2 : WithTop ℝ) ≤ weightedQuantile β (fun i => s (D.1 i))
        (fun i => w (D.1 i) / (∑ j, w (D.1 j) + w D.2))} = 1 := by
  simp [weightedQuantile]

/-- The covariate is a fair bit in training and always true at test time. At level one half,
a false calibration bit gives an infinite threshold; a true bit gives the calibration response,
including equality at the threshold. -/
example (κ : Kernel Bool ℝ) [IsMarkovKernel κ] :
    ENNReal.ofReal (1 / 2) ≤
      ((Measure.pi fun _ : Fin 1 => uniformOn (Set.univ : Set Bool) ⊗ₘ κ).prod
        (Measure.dirac true ⊗ₘ κ)) {D | (D.1 0).1 = false ∨ D.2.2 ≤ (D.1 0).2} := by
  let μ := uniformOn (Set.univ : Set Bool)
  let ν := Measure.dirac true
  have hac : ν ≪ μ := by
    intro A hA
    have hempty : A = ∅ := by
      simpa only [Set.univ_inter] using (uniformOn_eq_zero_iff Set.finite_univ).mp hA
    simp [hempty]
  have hratio (b : Bool) : (ν.rnDeriv μ b).toReal = if b then 2 else 0 := by
    have h := Measure.setLIntegral_rnDeriv hac {b}
    have hmass : μ {b} = 1 / 2 := by
      dsimp only [μ]
      rw [uniformOn_univ]
      simp
    rw [lintegral_singleton, hmass] at h
    have hreal := congrArg ENNReal.toReal h
    cases b <;> norm_num [ν, ENNReal.toReal_mul] at hreal ⊢ <;> linarith
  have h := le_measure_score_le_weightedQuantile μ ν hac κ measurable_snd
    (α := 1 / 2) (by norm_num) (by norm_num) 1
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at h
  refine h.trans_eq (congrArg ((Measure.pi fun _ : Fin 1 => μ ⊗ₘ κ).prod (ν ⊗ₘ κ)) ?_)
  ext D
  rw [Set.mem_ofPred_eq, coe_le_weightedQuantile_iff (by norm_num) _
    (fun i => div_nonneg ENNReal.toReal_nonneg
      (add_nonneg (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg) ENNReal.toReal_nonneg))]
  simp only [Finset.sum_filter, Fin.sum_univ_one, hratio, Set.mem_ofPred_eq]
  cases hc : (D.1 0).1 <;> cases ht : D.2.1 <;>
    by_cases hlt : (D.1 0).2 < D.2.2 <;> norm_num [hlt, ← not_lt]

end MathlibExtTest.Probability.Statistics.ConformalCovariateShift
