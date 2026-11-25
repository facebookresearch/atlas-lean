/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.UncoupledDynamics
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

open MathlibExt.GameTheory.UncoupledDynamicsWanted

-- Varying the last player's parameter moves only the first player's probability.
example (t : ℝ) : jordanEq ![1, 1, t] = ![t / (t + 1), 1 / 2, 1 / 2] := by
  funext i
  fin_cases i <;> norm_num [jordanEq, Fin.reduceSub]

-- Every positive parameter gives an interior probability.
example (a : Fin 3 → ℝ) (ha : ∀ i, 0 < a i) (i : Fin 3) :
    jordanEq a i ∈ Set.Ioo 0 1 := by
  have hp := ha (i - 1)
  exact ⟨div_pos hp (by positivity), (div_lt_one (by positivity)).2 (lt_add_one _)⟩
