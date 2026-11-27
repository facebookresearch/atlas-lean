/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Probability.Statistics.NeymanScott

open WantedExt.Probability.Statistics.NeymanScottWanted

-- One equal pair at a nonzero observation already gives unbounded likelihood.
example : ∃ s : ℝ, 0 < s ∧ 10 < logLik (fun (_ : Fin 1) (_ : Fin 2) => 3) (fun _ => 3) s := by
  exact logLik_unbounded (by decide) (fun _ _ => 3) (fun _ => rfl) 10

-- At this variance the normalizing term is nonzero, so this also checks the two summands.
example : logLik (fun (_ : Fin 1) (_ : Fin 2) => 3) (fun _ => 3)
    (Real.exp 1 / (2 * Real.pi)) = -1 := by
  have hπ : 2 * Real.pi ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  norm_num [logLik, Fin.sum_univ_one, Fin.sum_univ_two, mul_div_cancel₀ _ hπ, Real.log_exp]

private noncomputable def onePair (_ : Fin 1) (t : Fin 2) : ℝ :=
  if t = 0 then 0 else 2

private theorem onePair_diff_pos : 0 < ∑ i, (onePair i 0 - onePair i 1) ^ 2 := by
  norm_num [onePair, Fin.sum_univ_one]

private theorem onePair_mean : (fun i => (onePair i 0 + onePair i 1) / 2) = fun _ => 1 := by
  funext i
  norm_num [onePair]

private theorem onePair_variance : mleVariance onePair = 1 := by
  norm_num [mleVariance, onePair, Fin.sum_univ_one]

-- The pair (0, 2) attains the maximum at mean and variance both equal to 1.
example : logLik onePair (fun _ => 1) 1 =
    logLik onePair (fun i => (onePair i 0 + onePair i 1) / 2) (mleVariance onePair) :=
  (logLik_max onePair onePair_diff_pos (fun _ => 1) 1 one_pos).2.mpr
    ⟨onePair_mean.symm, onePair_variance.symm⟩

-- Changing just the mean strictly decreases the log-likelihood.
example : logLik onePair (fun _ => 0) 1 < logLik onePair (fun _ => 1) 1 := by
  have h := logLik_max onePair onePair_diff_pos (fun _ => 0) 1 one_pos
  rw [onePair_mean, onePair_variance] at h
  refine lt_of_le_of_ne h.1 fun heq => ?_
  have hmean := congrFun (h.2.mp heq).1 0
  norm_num at hmean
