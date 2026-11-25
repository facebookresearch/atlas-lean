/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.PotentialMethod
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith

/-!
# Tests for the potential method

Tarjan's stack example: with potential equal to the stack size, an operation popping `k`
items and pushing one has actual cost `k + 1` and amortized cost `2`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.PotentialMethodTests

open PotentialMethod

/-- Stack sizes along a run: three pushes, then one operation popping three and pushing one. -/
def sizes : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | _ => 1

/-- Actual costs: one per push, plus one per pop. -/
def costs : ℕ → ℤ
  | 3 => 4
  | _ => 1

/-- Every operation of the run has amortized cost `2`. -/
example : ∀ i < 4, amortizedCost (fun n : ℕ => (n : ℤ)) sizes costs i = 2 := by
  intro i hi
  interval_cases i <;> simp [amortizedCost, sizes, costs]

/-- The telescoping identity on this run: `7 = 8 + 0 - 1`. -/
example : ∑ i ∈ Finset.range 4, costs i =
    ∑ i ∈ Finset.range 4, amortizedCost (fun n : ℕ => (n : ℤ)) sizes costs i +
      (sizes 0 : ℤ) - (sizes 4 : ℤ) :=
  sum_cost_eq _ sizes costs 4

/-- Per-operation amortized bounds give the total bound `4 · 2 + Φ₀ - Φ₄ = 7`. -/
example : ∑ i ∈ Finset.range 4, costs i ≤
    ∑ _i ∈ Finset.range 4, (2 : ℤ) + (sizes 0 : ℤ) - (sizes 4 : ℤ) :=
  sum_cost_le_of_amortizedCost_le (fun n : ℕ => (n : ℤ)) sizes costs (fun _ => 2) 4
    (fun i hi => by interval_cases i <;> simp [amortizedCost, sizes, costs])

end Cslib.Algorithms.Lean.PotentialMethodTests
