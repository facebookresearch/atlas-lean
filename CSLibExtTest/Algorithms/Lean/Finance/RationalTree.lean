/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Finance.RationalTree
public import MathlibExt.Probability.OptimalStopping.FiniteBinomialTree
public import Mathlib.Data.Rat.Cast.Order

/-!
# Tests for the rational finite-tree evaluator

All-date early exercise (value `10`) against the terminal-only restricted
value `1`, no-early-exercise, horizon zero, probability endpoints, and a
non-unit gross return discriminating division by `R`.
-/

namespace Cslib.Algorithms.Lean.Finance.RationalTree

/-- Exercise payoff by history length: `0` at the root, `10` one step out,
`1` thereafter. -/
def gW : List Bool → Rat
  | [] => 0
  | [_] => 10
  | _ :: _ :: _ => 1

/-- Exercise payoff by history length: `1` at the root and one step out,
`10` thereafter. -/
def gN : List Bool → Rat
  | [] => 1
  | [_] => 1
  | _ :: _ :: _ => 10

/-- All-date early exercise: with two periods left, exercising one step out
dominates, so the root value is `10`. -/
theorem snellRat_gW_allDate : snellRat (1 / 2) 1 gW 2 [] = 10 := by
  decide +kernel

/-- Cast of the all-date value equals the native real Snell value. -/
theorem snellRat_cast_gW_allDate :
    ((snellRat (1 / 2) 1 gW 2 [] : Rat) : Real)
      = MathlibExt.Economics.Finance.BinomialOptimalStopping.snell
          (1 / 2 : Real) 1 (fun t => ((gW t : Rat) : Real)) 2 [] := by
  have h := snellRat_cast_eq_snell (1 / 2) 1 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) gW 2 []
  norm_num at h ⊢
  exact h

/-- Native real Snell value at the all-date point is `10`, via the cast
theorem and the rational computation. -/
theorem snell_gW_allDate_native :
    MathlibExt.Economics.Finance.BinomialOptimalStopping.snell
      (1 / 2 : Real) 1 (fun t => ((gW t : Rat) : Real)) 2 [] = 10 := by
  rw [← snellRat_cast_gW_allDate, snellRat_gW_allDate]
  norm_num

/-- Terminal-only witness: never stopping early (mandatory terminal payoff)
yields `1` at the root, differing from the unrestricted Snell value `10`. -/
theorem ruleValue_gW_european :
    MathlibExt.Economics.Finance.BinomialOptimalStopping.ruleValue
      (1 / 2 : Real) 1 (fun t => ((gW t : Rat) : Real))
      (stop := fun _ _ => false) 2 [] = 1 := by
  simp only [MathlibExt.Economics.Finance.BinomialOptimalStopping.ruleValue,
    MathlibExt.Economics.Finance.BinomialOptimalStopping.continuation,
    gW, Bool.false_eq_true, ite_false]
  norm_num

/-- No early exercise: continuation dominates at both pre-terminal dates,
value `10`. -/
theorem snellRat_gN_noEarlyExercise : snellRat (1 / 2) 1 gN 2 [] = 10 := by
  decide +kernel

/-- Horizon `0` returns the exercise payoff, here `10`. -/
theorem snellRat_gW_horizon0 : snellRat (1 / 3) 2 gW 0 [true] = 10 := by
  decide +kernel

/-- Up-probability endpoints still allow reaching the `10` payoff. -/
theorem snellRat_gW_q0 : snellRat 0 1 gW 2 [] = 10 := by
  decide +kernel

theorem snellRat_gW_q1 : snellRat 1 1 gW 2 [] = 10 := by
  decide +kernel

/-- Gross return `R ≠ 1` discrimination: continuation `10 / 2` beats
exercising for `0` at the root, value `5`. -/
theorem snellRat_gW_Rdiscrim : snellRat (1 / 2) 2 gW 1 [] = 5 := by
  decide +kernel

end Cslib.Algorithms.Lean.Finance.RationalTree
