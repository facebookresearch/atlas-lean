/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Complexity.BooleanFormula

/-! Tests for `Cslib.Complexity.BooleanFormula`: evaluation, depth and size of small formulas, and
a substitution that copies a repeated input, checked exactly and against the public bounds. -/

@[expose] public section

namespace Cslib.Complexity.BooleanFormulaTests

open Cslib.Complexity

/-- Computation: an AND of the two inputs evaluates as expected. -/
example : BooleanFormula.eval (fun i : Fin 2 => decide (i = 0))
    (BooleanFormula.and (BooleanFormula.input 0) (BooleanFormula.input 1)) = false := rfl

/-- Computation: NOT of a constant. -/
example : BooleanFormula.eval (fun _ : Fin 0 => true)
    (BooleanFormula.not (BooleanFormula.const true)) = false := rfl

/-- The depth and size of a one-gate formula. -/
example : (BooleanFormula.and (BooleanFormula.input (0 : Fin 2))
    (BooleanFormula.const true)).depth = 1 ∧
    (BooleanFormula.and (BooleanFormula.input (0 : Fin 2))
    (BooleanFormula.const true)).size = 1 := ⟨rfl, rfl⟩

/-- Outer formula `x₀ ∧ (x₀ ∨ x₁)`, which reads input `0` twice. -/
def outer : BooleanFormula 2 :=
  .and (.input 0) (.or (.input 0) (.input 1))

/-- Wiring `x₀ ↦ ¬y₀` and `x₁ ↦ y₀ ∧ y₁`: one gate and depth one each. -/
def wiring : Fin 2 → BooleanFormula 2
  | 0 => .not (.input 0)
  | 1 => .and (.input 0) (.input 1)

/-- Substitution copies `¬y₀` at both occurrences of input `0`. -/
example : outer.subst wiring =
    .and (.not (.input 0)) (.or (.not (.input 0)) (.and (.input 0) (.input 1))) := rfl

/-- Exact evaluation of the substituted formula at `y = (false, true)`, and `eval_subst` there. -/
example : (outer.subst wiring).eval (fun i : Fin 2 => decide (i = 1)) = true ∧
    (outer.subst wiring).eval (fun i : Fin 2 => decide (i = 1)) =
      outer.eval (fun i => (wiring i).eval (fun j : Fin 2 => decide (j = 1))) :=
  ⟨rfl, BooleanFormula.eval_subst wiring outer (fun i : Fin 2 => decide (i = 1))⟩

/-- Exact depth `3` and size `5` of the substituted formula. -/
example : (outer.subst wiring).depth = 3 ∧ (outer.subst wiring).size = 5 := ⟨rfl, rfl⟩

/-- The public bounds with `D = 1`: depth `3 ≤ 2 + 1`, the tight size bound `5 ≤ 2 * 2 + 1`
(attained here), and the weaker size bound `5 ≤ 2 * 2 + 2`. -/
example : (outer.subst wiring).depth ≤ outer.depth + 1 ∧
    (outer.subst wiring).size ≤ outer.size * (1 + 1) + 1 ∧
    (outer.subst wiring).size ≤ outer.size * (1 + 1) + (1 + 1) := by
  have hdepth : ∀ i, (wiring i).depth ≤ 1 := by decide
  have hsize : ∀ i, (wiring i).size ≤ 1 := by decide
  exact ⟨BooleanFormula.depth_subst_le wiring outer 1 hdepth,
    BooleanFormula.size_subst_le_tight wiring outer 1 hsize,
    BooleanFormula.size_subst_le wiring outer 1 hsize⟩

end Cslib.Complexity.BooleanFormulaTests
