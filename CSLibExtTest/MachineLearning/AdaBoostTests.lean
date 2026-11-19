/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.AdaBoost

import Mathlib.Tactic.FinCases

/-!
# AdaBoost tests

Closed checks: the training-error bounds instantiated for ten training points and a weak learner
with edge `1 / 10`, plus the round normalizer at error `1 / 4`. A concrete three-point run has
one-round edge `1 / 6` while its learner violates the stronger global `WeakLearner` assumption;
the direct round-error theorem still applies. The zero-round boundary is also checked.
The definitions are real-valued and not executable.
-/

namespace Cslib.MachineLearning.AdaBoost

open Real

example (y : Fin 10 → Bool) (wl : (Fin 10 → ℝ) → Fin 10 → Bool) (hwl : WeakLearner y wl (1 / 10))
    (T : ℕ) : trainErr y wl T ≤ exp (-2 * (1 / 10) ^ 2 * T) :=
  trainErr_le_exp (by norm_num) (by norm_num) hwl T

-- at error `1 / 4` a round multiplies the bound by `2 √(3 / 16) = √3 / 2`
example : 2 * sqrt ((1 / 4 : ℝ) * (1 - 1 / 4)) = sqrt 3 / 2 := by
  rw [show (1 / 4 : ℝ) * (1 - 1 / 4) = 3 / 16 by norm_num, sqrt_div' _ (by norm_num : (0:ℝ) ≤ 16),
    show (16 : ℝ) = 4 ^ 2 by norm_num, sqrt_sq (by norm_num)]
  ring

private def labels3 : Fin 3 → Bool := fun _ => false

private def learner3 (_ : Fin 3 → ℝ) : Fin 3 → Bool := fun i => decide (i = 0)

private theorem eps_learner3_zero : eps labels3 learner3 0 = (1 / 3 : ℝ) := by
  norm_num [eps, hyp, dist, err, labels3, learner3, Fin.sum_univ_three]

example : ∀ t < 1, 0 < eps labels3 learner3 t ∧
    eps labels3 learner3 t ≤ 1 / 2 - (1 / 6 : ℝ) := by
  intro t ht
  have ht0 : t = 0 := by omega
  subst t
  rw [eps_learner3_zero]
  norm_num

example : ¬ WeakLearner labels3 learner3 (1 / 6) := by
  intro h
  let D : Fin 3 → ℝ := fun i => if i = 0 then 3 / 4 else 1 / 8
  have hD : ∀ i, 0 < D i := by
    intro i
    fin_cases i <;> norm_num [D]
  have hsum : ∑ i, D i = 1 := by
    norm_num [D, Fin.sum_univ_three]
  have hbound := (h D hD hsum).2
  norm_num [err, labels3, learner3, D, Fin.sum_univ_three] at hbound

example : trainErr labels3 learner3 1 ≤ exp (-2 * (1 / 6 : ℝ) ^ 2 * ((1 : ℕ) : ℝ)) := by
  apply trainErr_le_exp_of_round_errors (y := labels3) (wl := learner3)
    (γ := (1 / 6 : ℝ)) (by decide) (by norm_num) 1
  intro t ht
  have ht0 : t = 0 := by omega
  subst t
  rw [eps_learner3_zero]
  norm_num

example : trainErr labels3 learner3 0 ≤ exp (-2 * (1 / 6 : ℝ) ^ 2 * ((0 : ℕ) : ℝ)) := by
  apply trainErr_le_exp_of_round_errors (y := labels3) (wl := learner3)
    (γ := (1 / 6 : ℝ)) (by decide) (by norm_num) 0
  intro t ht
  omega

#print axioms trainErr_le_prod_sqrt_of_round_errors
#print axioms trainErr_le_exp_of_round_errors
#print axioms trainErr_le_exp
#print axioms trainErr_le_prod_sqrt

end Cslib.MachineLearning.AdaBoost
