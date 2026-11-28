/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Domains.Biology.StatisticalGenetics.AssociationTests.ConditionalLogisticMatchedSets
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tests for matched-set conditional case probabilities
-/

open WantedExt.Biology.StatisticalGenetics.ConditionalLogisticMatchedSetsWanted

private def pairExposures (i : Fin 2) (_ : Fin 1) : ℝ := i.val

-- The exposures 0 and 1 are both shifted by 3, with a nonzero coefficient.
example (α : ℝ) :
    conditionalCaseProb (M := 1) α (fun _ => Real.log 2) (fun i => pairExposures i + fun _ => 3) 0 =
      conditionalCaseProb (M := 1) α (fun _ => Real.log 2) pairExposures 0 :=
  conditionalCaseProb_add_const α (fun _ => Real.log 2) pairExposures (fun _ => 3) 0

-- At coefficient log 2, the two unshifted weights are 1 and 2, regardless of the intercept.
example (α : ℝ) :
    conditionalCaseProb (M := 1) α (fun _ => Real.log 2) pairExposures 0 = 1 / 3 := by
  rw [conditionalCaseProb_eq, Fin.sum_univ_two]
  simp [dotProduct, pairExposures, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

-- For discordant counts (2, 1), evaluate the pair probabilities at the proposed maximizer.
private theorem sigmoid_log_two : Real.sigmoid (Real.log 2) = 2 / 3 := by
  rw [Real.sigmoid_def, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

private theorem sigmoid_neg_log_two : Real.sigmoid (-Real.log 2) = 1 / 3 := by
  rw [Real.sigmoid_neg, sigmoid_log_two]
  norm_num

private theorem fitted_pair_probs :
    Real.sigmoid (-Real.log 2 + 2 * Real.log 2) * (1 - Real.sigmoid (-Real.log 2)) = 4 / 9 ∧
      Real.sigmoid (-Real.log 2) * (1 - Real.sigmoid (-Real.log 2 + 2 * Real.log 2)) = 1 / 9 := by
  rw [show -Real.log 2 + 2 * Real.log 2 = Real.log 2 by ring,
    sigmoid_log_two, sigmoid_neg_log_two]
  norm_num

-- Compute the public likelihood at zero and at the fit, independently of the maximizer theorem.
example : perPairInterceptLogLik (fun _ : Fin 2 => 0) (fun _ : Fin 1 => 0) 0 <
    perPairInterceptLogLik (fun _ : Fin 2 => -Real.log 2) (fun _ : Fin 1 => -Real.log 2)
      (2 * Real.log 2) := by
  calc
    _ = Real.log (1 / 64) := by
      rw [perPairInterceptLogLik_const]
      norm_num [Real.sigmoid_zero]
      rw [two_mul, ← Real.log_mul (x := 1 / 4) (y := 1 / 4) (by norm_num) (by norm_num),
        ← Real.log_mul (x := 1 / 4 * (1 / 4)) (y := 1 / 4) (by norm_num) (by norm_num)]
      norm_num
    _ < Real.log (16 / 729) := Real.log_lt_log (by norm_num) (by norm_num)
    _ = _ := by
      rw [perPairInterceptLogLik_const, fitted_pair_probs.1, fitted_pair_probs.2]
      norm_num
      rw [two_mul, ← Real.log_mul (x := 4 / 9) (y := 4 / 9) (by norm_num) (by norm_num),
        ← Real.log_mul (x := 4 / 9 * (4 / 9)) (y := 1 / 9) (by norm_num) (by norm_num)]
      norm_num

-- At zero slope, displacing an intercept from zero strictly decreases that pair's probability.
example : Real.sigmoid (Real.log 2) * (1 - Real.sigmoid (Real.log 2)) = 2 / 9 ∧
    Real.sigmoid (Real.log 2) * (1 - Real.sigmoid (Real.log 2)) <
      Real.sigmoid 0 * (1 - Real.sigmoid 0) := by
  rw [sigmoid_log_two, Real.sigmoid_zero]
  norm_num

example : Real.exp (2 * Real.log 2) = (2 : ℝ) ^ 2 := by
  rw [two_mul, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2), pow_two]

-- Client example: the two exposed-case pairs may have different intercepts.
example : perPairInterceptLogLik ![0, Real.log 2] (fun _ : Fin 1 => 0) 0 ≤
    perPairInterceptLogLik (fun _ : Fin 2 => -Real.log 2) (fun _ : Fin 1 => -Real.log 2)
      (2 * Real.log 2) := by
  simpa using perPairInterceptLogLik_le (n₁₀ := 2) (n₀₁ := 1) (by decide) (by decide)
    ![0, Real.log 2] (fun _ => 0) 0
