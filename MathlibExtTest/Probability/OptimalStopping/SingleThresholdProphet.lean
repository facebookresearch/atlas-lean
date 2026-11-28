/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.OptimalStopping.SingleThresholdProphet
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # Tie handling, no acceptance, and the two-prize sharpness example -/

open MeasureTheory ProbabilityTheory Set

private def prizes (i : Fin 2) (_ : Unit) : ℝ := if i = 0 then 1 else 2

-- The maximum is 2, so the threshold is 1. Accepting a tie gives the first prize;
-- rejecting it gives the second. A threshold above both prizes gives zero.
example : singleThresholdReward prizes (Ici 1) () = 1 ∧
    singleThresholdReward prizes (Ioi 1) () = 2 ∧
    singleThresholdReward prizes (Ioi 2) () = 0 := by
  have hlt (i j : Fin 2) : i < j ↔ i = 0 ∧ j = 1 := by
    fin_cases i <;> fin_cases j <;> decide
  have hall (p : Fin 2 → Prop) : (∀ i, p i) ↔ p 0 ∧ p 1 := by
    refine ⟨fun h => ⟨h 0, h 1⟩, fun h i => ?_⟩
    fin_cases i
    · exact h.1
    · exact h.2
  classical
  unfold singleThresholdReward
  norm_num [Fin.sum_univ_two, prizes, Set.indicator, hall, hlt]

example :
    let half : Set.Icc (0 : ℝ) 1 := ⟨1 / 2, by constructor <;> norm_num⟩
    let μ := bernoulliMeasure (2 : ℝ) 0 half
    (∫ x, max (1 : ℝ) x ∂μ) = 3 / 2 ∧
      ∀ (d₁ : ℝ → Bool) (d₂ : ℝ → ℝ → Bool),
        (∫ x, if d₁ 1 then (1 : ℝ) else if d₂ 1 x then x else 0 ∂μ) ≤ 1 := by
  intro half μ
  have h := single_threshold_prophet_two_prize_sharpness half (by norm_num [half])
  norm_num [half] at h
  exact h
