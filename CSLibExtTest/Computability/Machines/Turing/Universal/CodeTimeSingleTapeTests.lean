/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Machines.Turing.Universal.CodeTimeSingleTape
public meta import CSLibExt.Computability.Machines.Turing.Universal.CodeTimeSingleTape

@[expose] public section

/-!
# Tests for codes on CSLib's single-tape machines

The constant-`false` code `Code.constFalse` leaves its input left of its head, so its single-tape
machine halts with the answer under the head but does not output `[false]` in CSLib's convention.
`eraseFalse` blanks its input as it goes and then writes the answer, so its single-tape machine
outputs `[false]` within `2 n + 2` steps, also on the empty input. The code with an empty table
halts at once, and its single-tape machine halts within one step but not within `0` steps, so the
`+ 1` in the step bounds is needed. Three more codes run step by step on their single-tape
machines: `writeLarge` writes the symbol `37`, `eraseMove` writes the blank and moves left, and
`drift` never halts.
-/

set_option autoImplicit false

namespace CSLibExtTest.Computability.Machines.Turing.Universal.CodeTimeSingleTape

open Relation Cslib.Turing Cslib.Turing.Universal

/-- The largest action number of the constant-`false` code is `3` (write `1`). -/
example : Code.constFalse.symBound = 6 := by decide

/-- The code with an empty table uses only the blank and the two input symbols. -/
example : (⟨[]⟩ : Code).symBound = 3 := rfl

/-- Distinct bits have distinct input symbols. -/
example : Code.constFalse.inputSym true ≠ Code.constFalse.inputSym false :=
  fun h ↦ Bool.noConfusion (Code.inputSym_injective _ h)

/-- The code with an empty table halts at once: on `[true]` its single-tape machine halts within
one step, the step into its halting state, with a tape that reads as the tape of the code. -/
example : ∃ tape, RelatesWithinSteps (⟨[]⟩ : Code).singleTapeTM.TransitionRelation
      ((⟨[]⟩ : Code).singleTapeTM.initCfg ([true].map (⟨[]⟩ : Code).inputSym)) ⟨none, tape⟩ 1 ∧
    (SingleTapeTM.toTape tape).map (⟨[]⟩ : Code).symVal =
      ((⟨[]⟩ : Code).cfgAfter [true] 0).toTM0.Tape :=
  Code.exists_relatesWithinSteps_singleTapeTM rfl

/-- `constFalse` decides the empty language within `n + 1` steps, so on every input its
single-tape machine halts within `n + 2` steps, with the answer `false` under the head and every
cell right of the head blank. -/
example (x : List Bool) : ∃ left,
    RelatesWithinSteps Code.constFalse.singleTapeTM.TransitionRelation
      (Code.constFalse.singleTapeTM.initCfg (x.map Code.constFalse.inputSym))
      ⟨none, ⟨some (Code.constFalse.inputSym false), left, ∅⟩⟩ (x.length + 2) := by
  obtain ⟨left, -, h⟩ := Code.constFalse_decidesWithin.exists_relatesWithinSteps_singleTapeTM x
  exact ⟨left, h⟩

/-- After `2` steps on `[true]`, `constFalse` has halted with the input symbol `2` left of its
head. -/
example : Code.constFalse.cfgAfter [true] 2 = ⟨1, [2], 1, []⟩ := by decide

/-- So the single-tape machine of `constFalse` does not output `[false]` on the input `[true]` in
CSLib's convention, after any number of steps: the hypothesis on the cells left of the head in
`Code.DecidesWithin.outputsWithinTime_singleTapeTM` cannot be dropped. -/
example : ¬Code.constFalse.singleTapeTM.Outputs ([true].map Code.constFalse.inputSym)
    [Code.constFalse.inputSym false] := fun h ↦
  absurd ((Code.constFalse_decidesWithin.outputs_singleTapeTM_iff [true]).1 h 2 (by decide))
    (by decide)

/-- A code that answers `false` and leaves only the answer on the tape: in state `0` it
overwrites an input symbol with the blank and enters state `2`, which moves right and returns to
state `0`; on the first blank, state `0` writes `bitSym false = 1` and enters state `1`, whose
row is empty, so it halts. -/
def eraseFalse : Code := ⟨[[some (1, 3), some (2, 2), some (2, 2)], [], [some (0, 1)]]⟩

/-- The run of `eraseFalse` from the start of the rest `v` of its input. -/
theorem eraseFalse_iterate (v : List Bool) (L : List ℕ) :
    eraseFalse.stepOrStay^[2 * v.length + 1] ⟨0, L, (input v).headI, (input v).tail⟩ =
      ⟨1, List.replicate v.length 0 ++ L, 1, []⟩ := by
  induction v generalizing L with
  | nil => rfl
  | cons b v ih =>
    rw [List.length_cons, show 2 * (v.length + 1) + 1 = (2 * v.length + 1) + 2 by ring,
      Function.iterate_add_apply]
    have hs : eraseFalse.stepOrStay^[2] ⟨0, L, (input (b :: v)).headI, (input (b :: v)).tail⟩ =
        ⟨0, 0 :: L, (input v).headI, (input v).tail⟩ := by
      cases b <;> rfl
    rw [hs, ih]
    simp [List.replicate_succ']

/-- `eraseFalse` decides the empty language within `2 n + 1` steps. -/
theorem eraseFalse_decidesWithin :
    eraseFalse.DecidesWithin (fun _ ↦ false) (fun n ↦ 2 * n + 1) := by
  intro x
  rw [Code.evalSteps_eq_some_iff_output, Code.cfgAfter, Code.init, eraseFalse_iterate x []]
  exact ⟨rfl, rfl⟩

/-- `eraseFalse` leaves only blanks left of its head. -/
theorem eraseFalse_left_blank (x : List Bool) :
    ∀ a ∈ (eraseFalse.cfgAfter x (2 * x.length + 1)).left, a = 0 := by
  rw [Code.cfgAfter, Code.init, eraseFalse_iterate x []]
  simp

/-- So the single-tape machine of `eraseFalse` outputs `[false]` in CSLib's convention within
`2 n + 2` steps, on every input. -/
example (x : List Bool) :
    eraseFalse.singleTapeTM.OutputsWithinTime (x.map eraseFalse.inputSym)
      [eraseFalse.inputSym false] (2 * x.length + 2) :=
  eraseFalse_decidesWithin.outputsWithinTime_singleTapeTM (eraseFalse_left_blank x)

/-- On the empty input it outputs `[false]` within `2` steps: the write of the answer and the step
into the halting state. -/
example : eraseFalse.singleTapeTM.OutputsWithinTime [] [eraseFalse.inputSym false] 2 :=
  eraseFalse_decidesWithin.outputsWithinTime_singleTapeTM (x := []) (eraseFalse_left_blank [])

/-- The same output, through `Code.DecidesWithin.outputs_singleTapeTM_iff`. -/
example (x : List Bool) :
    eraseFalse.singleTapeTM.Outputs (x.map eraseFalse.inputSym) [eraseFalse.inputSym false] :=
  (eraseFalse_decidesWithin.outputs_singleTapeTM_iff x).2 (eraseFalse_left_blank x)

/-- The code with an empty table halts on the empty input after `0` steps, with the empty
output. -/
example : (⟨[]⟩ : Code).evalSteps [] 0 = some [] := rfl

/-- Its single-tape machine outputs `[]` on the empty input within one step, the step into its
halting state. -/
example : (⟨[]⟩ : Code).singleTapeTM.OutputsWithinTime [] [] 1 :=
  ⟨1, le_rfl, .single rfl⟩

/-- But not within `0` steps: the `+ 1` in `Code.exists_relatesWithinSteps_singleTapeTM` and
`Code.DecidesWithin.outputsWithinTime_singleTapeTM` cannot be dropped, even for a code that halts
at once. -/
example : ¬(⟨[]⟩ : Code).singleTapeTM.OutputsWithinTime [] [] 0 := by
  rintro ⟨n, hn, hr⟩
  have hz : n = 0 := Nat.eq_zero_of_le_zero hn
  subst n
  have he := hr.zero
  exact Option.some_ne_none _ (congrArg SingleTapeTM.Cfg.state he)

/-- The configuration of the single-tape machine of `c` after `n` steps on the input word of `x`,
and `none` after the step past its halting configuration. -/
private def run (c : Code) (x : List Bool) (n : ℕ) : Option c.singleTapeTM.Cfg :=
  (flip bind c.singleTapeTM.step)^[n] (some (c.singleTapeTM.initCfg (x.map c.inputSym)))

/-- Whether the single-tape machine of `c` has halted after `n` steps on the input word of `x`,
with the cell under its head and the nearest cells left and right of it, read as numbers. -/
private def observe (c : Code) (x : List Bool) (n : ℕ) : Option (Bool × ℕ × ℕ × ℕ) :=
  (run c x n).map fun d ↦
    let tape := (SingleTapeTM.toTape d.BiTape).map c.symVal
    (d.state.isNone, tape.head, tape.left.nth 0, tape.right.nth 0)

-- On the empty input `constFalse` writes its answer, then takes the step into its halting state.
#guard observe Code.constFalse [] 1 = some (false, 1, 0, 0)
#guard observe Code.constFalse [] 2 = some (true, 1, 0, 0)

/-- A code that writes the symbol `37`: in state `0` on the blank it writes `37` (action number
`39`) and enters state `1`, which has no row, so it halts. -/
private def writeLarge : Code := ⟨[[some (1, 39)]]⟩

/-- The alphabet of `writeLarge` has `39 + 3` symbols, so it holds the symbol `37`. -/
example : writeLarge.symBound = 42 := by decide

/-- After one step on the empty input, `writeLarge` has halted with the output `[37]`. -/
example : writeLarge.evalSteps [] 1 = some [37] := rfl

-- Its single-tape machine halts after `2` steps with `37` under its head.
#guard observe writeLarge [] 2 = some (true, 37, 0, 0)

/-- So its single-tape machine halts on the empty input within `2` steps, with a tape that reads as
the tape of `writeLarge` after one step. -/
example : ∃ tape, RelatesWithinSteps writeLarge.singleTapeTM.TransitionRelation
      (writeLarge.singleTapeTM.initCfg (([] : List Bool).map writeLarge.inputSym))
      ⟨none, tape⟩ 2 ∧
    (SingleTapeTM.toTape tape).map writeLarge.symVal = (writeLarge.cfgAfter [] 1).toTM0.Tape :=
  Code.exists_relatesWithinSteps_singleTapeTM (c := writeLarge) (x := []) (T := 1) rfl

/-- A code that writes the blank and moves left: in state `0` it overwrites any symbol with the
blank (action number `2`) and enters state `1`, which on the blank moves left (action number `0`)
and enters state `2`, which has no row, so it halts. -/
private def eraseMove : Code := ⟨[[some (1, 2), some (1, 2), some (1, 2)], [some (2, 0)]]⟩

/-- After `2` steps on `[true, false]`, `eraseMove` has halted with the output `[0, 0, 1]`: the
blank it moved onto, the blank it wrote, and the input symbol of `false`. -/
example : eraseMove.evalSteps [true, false] 2 = some [0, 0, 1] := rfl

-- Its single-tape machine halts after `3` steps with blanks under its head and next to it.
#guard observe eraseMove [true, false] 3 = some (true, 0, 0, 0)

/-- So its single-tape machine halts on `[true, false]` within `3` steps, with a tape that reads as
the tape of `eraseMove` after `2` steps. -/
example : ∃ tape, RelatesWithinSteps eraseMove.singleTapeTM.TransitionRelation
      (eraseMove.singleTapeTM.initCfg ([true, false].map eraseMove.inputSym)) ⟨none, tape⟩ 3 ∧
    (SingleTapeTM.toTape tape).map eraseMove.symVal =
      (eraseMove.cfgAfter [true, false] 2).toTM0.Tape :=
  Code.exists_relatesWithinSteps_singleTapeTM (c := eraseMove) (x := [true, false]) (T := 2) rfl

/-- A code that never halts: in state `0` it moves right on every symbol. -/
private def drift : Code := ⟨[[some (0, 1), some (0, 1), some (0, 1)]]⟩

/-- `drift` has not halted after `3` steps on the empty input. -/
example : drift.evalSteps [] 3 = none := rfl

-- Nor has its single-tape machine after `4` steps.
#guard observe drift [] 4 = some (false, 0, 0, 0)

end CSLibExtTest.Computability.Machines.Turing.Universal.CodeTimeSingleTape
