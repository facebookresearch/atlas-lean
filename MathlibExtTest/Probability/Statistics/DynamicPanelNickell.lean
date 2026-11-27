/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.DynamicPanelNickell
import Mathlib.Tactic.NormNum

/-! # Regressions for the two-period dynamic-panel within slope -/

open MathlibExt.Probability.Statistics

-- A common unit effect does not change the two within cross products.
example (a : ℝ) :
    twoPeriodWithinProduct (fun t : Fin 2 => a + if t = 0 then 1 else -1)
        (fun t : Fin 2 => a + if t = 0 then -1 else 1) = -2 ∧
      twoPeriodWithinProduct (fun t : Fin 2 => a + if t = 0 then 1 else -1)
        (fun t : Fin 2 => a + if t = 0 then 1 else -1) = 2 := by
  norm_num [twoPeriodWithinProduct_eq]

-- Constant lags within each unit give a zero denominator, even if the unit means vary.
example (c : ℕ → ℝ) (y : ℕ → Unit → Fin 2 → ℝ) (N : ℕ) :
    PanelWithin.withinEstimator
      (fun i (_ : Unit) => Matrix.of fun (_ : Fin 2) (_ : Fin 1) => c i) y N () 0 = 0 := by
  rw [twoPeriodWithin_estimator_eq (fun i (_ : Unit) (_ : Fin 2) => c i)]
  simp [twoPeriodWithinProduct_eq]

-- A single unit with opposite changes in lag and response has positive Gram and slope −1/2.
example (a : ℝ) :
    let x : ℕ → Unit → Fin 2 → ℝ := fun _ _ t => a + if t = 0 then 0 else 2
    let y : ℕ → Unit → Fin 2 → ℝ := fun _ _ t => a + if t = 0 then 2 else 1
    let X := fun i w => Matrix.of fun t (_ : Fin 1) => x i w t
    PanelWithin.withinGram X 1 () 0 0 = 2 ∧ PanelWithin.withinEstimator X y 1 () 0 = -1 / 2 := by
  intro x y X
  rw [show X = _ from rfl, twoPeriodWithin_gram x, twoPeriodWithin_estimator_eq x]
  norm_num [x, y, twoPeriodWithinProduct_eq]
