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
