/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.AdaBoost

/-!
# AdaBoost tests

Closed checks: the training-error bounds instantiated for ten training points and a weak learner
with edge `1 / 10`, plus the round normalizer at error `1 / 4`. The definitions are real-valued and
not executable.
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

#print axioms trainErr_le_exp
#print axioms trainErr_le_prod_sqrt

end Cslib.MachineLearning.AdaBoost
