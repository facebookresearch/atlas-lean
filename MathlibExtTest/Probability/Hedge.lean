/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Hedge
import Mathlib.Tactic.NormNum

/-- Boundary check: the regret bound instantiates for two experts
over one round with uniform losses. -/
example (loss : Fin 1 → Fin 2 → ℝ)
    (hloss : ∀ t i, loss t i ∈ Set.Icc (0 : ℝ) 1) (i : Fin 2) :
    (∑ t, (∑ j, hedgeW loss 1 t j * loss t j) /
      (∑ j, hedgeW loss 1 t j)) ≤
      (∑ t, loss t i) + Real.log ((2 : ℕ) : ℝ) / 1 + 1 * ((1 : ℕ) : ℝ) / 8 :=
  hedge_regret (by norm_num) loss hloss (η := 1) (by norm_num) i

/-- At time zero no loss has accumulated, so every weight is `1`. -/
example (loss : Fin 3 → Fin 2 → ℝ) (η : ℝ) (t : Fin 3) (ht : t = 0)
    (i : Fin 2) : hedgeW loss η t i = 1 := by
  subst ht
  simp [hedgeW]
