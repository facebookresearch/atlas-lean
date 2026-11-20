/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Macro.ISLM
import Mathlib.Tactic.NormNum

@[expose] public section

namespace MathlibExtTest.Economics.Macro.ISLM

open MathlibExt.Economics.Macro.ISLM

/-- Concrete IS-LM: `b = h = k = 1`, `A = 10`, `M = 5` gives `Y = 15 / 2`, `r = 5 / 2`.
Prove by applying `islm_solution`. -/
theorem islm_example {Y r : ℝ} (h : IsISLM 1 1 1 10 5 Y r) :
    Y = 15 / 2 ∧ r = 5 / 2 := by
  obtain ⟨hY, hr⟩ := islm_solution zero_lt_one zero_lt_one zero_lt_one h
  norm_num at hY hr
  exact ⟨hY, hr⟩

/-- Concrete fiscal expansion: at `b = h = k = 1, M = 5`, moving `A` from `10` to `12`
moves the equilibrium from `(15 / 2, 5 / 2)` to `(17 / 2, 7 / 2)`: output and the interest
rate both rise. Prove by checking both systems and the two inequalities. -/
theorem islm_numeric_fiscal :
    IsISLM 1 1 1 10 5 (15 / 2) (5 / 2) ∧ IsISLM 1 1 1 12 5 (17 / 2) (7 / 2) ∧
      (15 / 2 : ℝ) < 17 / 2 ∧ (5 / 2 : ℝ) < 7 / 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [IsISLM]

/-- Concrete monetary expansion: at `b = h = k = 1, A = 10`, moving `M` from `5` to `7`
moves the equilibrium from `(15 / 2, 5 / 2)` to `(17 / 2, 3 / 2)`: output rises and the
interest rate falls. Prove by checking both systems and the two inequalities. -/
theorem islm_numeric_monetary :
    IsISLM 1 1 1 10 5 (15 / 2) (5 / 2) ∧ IsISLM 1 1 1 10 7 (17 / 2) (3 / 2) ∧
      (15 / 2 : ℝ) < 17 / 2 ∧ (3 / 2 : ℝ) < 5 / 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [IsISLM]

end MathlibExtTest.Economics.Macro.ISLM
