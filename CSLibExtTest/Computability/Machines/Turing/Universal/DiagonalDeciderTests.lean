/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Machines.Turing.Universal.DiagonalDecider

@[expose] public section

/-!
# Tests for the polynomial-time decider of the diagonal language

The cell-by-cell check and the layout on concrete inputs, and `P ⊄ CodeTime (n ↦ n ^ 2 + 1)`.
-/

set_option autoImplicit false

namespace CSLibExtTest.Computability.Machines.Turing.Universal.DiagonalDecider

open Cslib.Turing.Universal Cslib.Turing.Universal.Clocked Cslib.Turing.Universal.Diag

/-- The check accepts a code stack. -/
example : chkFrom 0 0 (codeCells Code.constFalse) = true := by
  rw [chkFrom_zero, isSome_decodeCodeCells_iff]
  exact ⟨_, rfl⟩

/-- The check rejects keys that do not increase: the entry `(0, 0, 0, 0)` twice. -/
example : chkFrom 0 0 (cells [0, 0, 0, 0, 0, 0, 0, 0]) = false := by decide +kernel

/-- The check rejects a list of units. -/
example : chkFrom 0 0 [true] = false := by decide +kernel

/-- The check agrees with `decodeCodeCells`. -/
example (x : List Bool) : chkFrom 0 0 x = (decodeCodeCells x).isSome := chkFrom_zero x

/-- The layout of the empty code stack: the clock `0 ^ 2 + 1 = 1`, no input cells, a blank
cell. -/
example : Layout.layout (true :: []) = [true, false, false] := by decide

/-- The layout on a bit list that does not start with `true` is the fixed list. -/
example : Layout.layout [false] = [false, true, true, false, false] := by decide

/-- The two machines write the universal machine's input. -/
example (x : List Bool) :
    Layout.layout (Check.answer x) =
      encIn (diagArg (fun n ↦ n ^ 2 + 1) x).1 (diagArg (fun n ↦ n ^ 2 + 1) x).2.1
        (diagArg (fun n ↦ n ^ 2 + 1) x).2.2 :=
  layout_answer x

/-- **The diagonal language is in `P`.** -/
example : diag (fun n ↦ n ^ 2 + 1) ∈ MetaMathlibExt.ComplexityTheory.P := diag_sq_add_one_mem_P

/-- **`P ⊄ CodeTime (n ↦ n ^ 2 + 1)`**, a class that is not empty. -/
example : ¬ MetaMathlibExt.ComplexityTheory.P ⊆ CodeTime (fun n ↦ n ^ 2 + 1) ∧
    (fun _ ↦ false) ∈ CodeTime (fun n ↦ n ^ 2 + 1) :=
  ⟨not_P_subset_codeTime_sq_add_one,
    const_false_mem_codeTime fun n ↦ Nat.add_le_add_right (Nat.le_self_pow two_ne_zero n) 1⟩

end CSLibExtTest.Computability.Machines.Turing.Universal.DiagonalDecider
