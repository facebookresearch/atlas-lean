/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.RepeatedPrisonersDilemma
public import Mathlib.Tactic.NormNum

/-! Examples for `MathlibExt.GameTheory.RepeatedPrisonersDilemma`: in the prisoner's dilemma
`(T, R, P, S) = (5, 3, 1, 0)` grim trigger satisfies the one-shot incentive inequalities at
`δ = 1/2` and violates them at `δ = 1/4`. -/

@[expose] public section

namespace MathlibExtTest.GameTheory.RepeatedPrisonersDilemma

open MathlibExt.GameTheory.RepeatedPrisonersDilemma

/-- The concrete prisoner's dilemma `(T, R, P, S) = (5, 3, 1, 0)` used to test
`oneShotIncentives_iff`: `T - R = 2` and `T - P = 4`, so the incentives hold at `δ = 1/2`
but fail at `δ = 1/4`. -/
def testPayoffs : Payoffs :=
  ⟨5, 3, 1, 0⟩

/-- At `δ = 1/2`, grim trigger satisfies the one-shot incentive inequalities. -/
theorem test_incentives_hold : OneShotIncentives testPayoffs (1 / 2) := by
  have hPS : testPayoffs.sucker ≤ testPayoffs.punishment := by norm_num [testPayoffs]
  have hδ1 : (1 / 2 : ℝ) ≤ 1 := by norm_num
  rw [oneShotIncentives_iff testPayoffs hPS hδ1]
  norm_num [testPayoffs]

/-- At `δ = 1/4`, grim trigger violates the one-shot incentive inequalities. -/
theorem test_incentives_fail : ¬ OneShotIncentives testPayoffs (1 / 4) := by
  have hPS : testPayoffs.sucker ≤ testPayoffs.punishment := by norm_num [testPayoffs]
  have hδ1 : (1 / 4 : ℝ) ≤ 1 := by norm_num
  rw [oneShotIncentives_iff testPayoffs hPS hδ1]
  norm_num [testPayoffs]

end MathlibExtTest.GameTheory.RepeatedPrisonersDilemma
