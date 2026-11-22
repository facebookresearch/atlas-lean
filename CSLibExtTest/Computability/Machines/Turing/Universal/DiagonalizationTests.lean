/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Machines.Turing.Universal.Diagonalization

@[expose] public section

/-!
# Tests for diagonalization against time-bounded codes

The constant-`false` code, the time classes of `n ↦ n ^ 2` (empty) and `n ↦ n ^ 2 + 1` (not
empty), the decoder and the diagonal language on concrete inputs, and the diagonal argument.
-/

set_option autoImplicit false

namespace CSLibExtTest.Computability.Machines.Turing.Universal.Diagonalization

open Cslib.Turing.Universal Cslib.Turing.Universal.Clocked

/-- On `[true, false, true]` the constant-`false` code needs four steps. -/
example : Code.constFalse.evalSteps [true, false, true] 4 = some [bitSym false] := by decide

/-- Three steps are not enough. -/
example : Code.constFalse.evalSteps [true, false, true] 3 = none := by decide

/-- The class of the bound `n ↦ n ^ 2 + 1` holds the empty language. -/
example : (fun _ ↦ false) ∈ CodeTime (fun n ↦ n ^ 2 + 1) :=
  const_false_mem_codeTime fun n ↦ Nat.add_le_add_right (Nat.le_self_pow two_ne_zero n) 1

/-- The class of the bound `n ↦ n ^ 2` is empty: no step on the empty input. -/
example : CodeTime (· ^ 2) = ∅ := codeTime_eq_empty rfl

/-- The empty bit list is the code stack of the code with no transitions, which halts at once
with an empty tape; so the empty list is in the diagonal language. -/
example : diag (fun n ↦ n ^ 2 + 1) [] = true := by
  rw [show ([] : List Bool) = codeCells ⟨[]⟩ from rfl, diag_codeCells]
  decide

/-- On its own code stack, the constant-`false` code answers `false` within the bound, so the
code stack is in the diagonal language. -/
example : diag (fun n ↦ n ^ 2 + 1) (codeCells Code.constFalse) = true := by
  rw [diag_codeCells, decide_eq_true_iff]
  have h := Code.evalSteps_mono (Code.constFalse_decidesWithin (codeCells Code.constFalse))
    (Nat.add_le_add_right (Nat.le_self_pow two_ne_zero (codeCells Code.constFalse).length) 1)
  rw [h]
  decide

/-- The code stack of a code decodes. -/
example : (decodeCodeCells (codeCells Code.constFalse)).isSome :=
  (isSome_decodeCodeCells_iff _).2 ⟨_, rfl⟩

/-- Code stacks end with a marker. -/
theorem getLast?_codeCells_ne (c : Code) : (codeCells c).getLast? ≠ some true := by
  simp only [codeCells, cells]
  cases h : entryNums (entries c) using List.reverseRecOn with
  | nil => simp
  | append_singleton l a => simp [cell]

/-- `[true]` is no code stack, so it is not in the diagonal language. -/
example : diag (fun n ↦ n ^ 2 + 1) [true] = false :=
  diag_eq_false fun c hc ↦ getLast?_codeCells_ne c (by rw [hc]; rfl)

/-- `[true]` does not decode. -/
example : decodeCodeCells [true] = none := by
  cases h : decodeCodeCells [true] with
  | none => rfl
  | some c =>
    have hc := codeCells_of_decodeCodeCells_eq_some h
    exact absurd (by rw [hc]; rfl) (getLast?_codeCells_ne c)

/-- One cell is no code stack: entries have four numbers. -/
example : decodeCodeCells [true, false] = none := by decide +kernel

/-- **The diagonal argument** for `n ↦ n ^ 2 + 1`, a bound whose class is not empty. -/
example : diag (fun n ↦ n ^ 2 + 1) ∉ CodeTime (fun n ↦ n ^ 2 + 1) := diag_not_mem_codeTime _

end CSLibExtTest.Computability.Machines.Turing.Universal.Diagonalization
