/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Machines.Turing.MultiTape.Code

@[expose] public section

/-!
# Tests for codes of multi-tape machines

Two small codes: `firstBit` (no work tapes) outputs the first input bit, or `false` on the empty
input, and halts; `lastBit` (one work tape) copies the input onto its work tape, steps back one
cell and outputs the last bit, exercising writes and both head moves on the zipper tapes. The
evaluator is run by `decide`; the agreement theorems then transfer the results to the decoded
machines of CSLib's model.
-/

set_option autoImplicit false

open Cslib.Turing.MultiTapeTM _root_.Turing

namespace CSLibExtTest.Computability.Machines.Turing.MultiTape

/-! ### No work tapes -/

/-- The code that outputs the first input bit (`false` on the empty input) and halts. -/
def firstBit : Code 0 :=
  ⟨[((0, some true, Fin.elim0), ⟨1, Fin.elim0, some true, none⟩),
    ((0, some false, Fin.elim0), ⟨1, Fin.elim0, some false, none⟩),
    ((0, none, Fin.elim0), ⟨1, Fin.elim0, some false, none⟩)]⟩

example : firstBit.evalSteps [true, false] 1 = some [true] := by decide
example : firstBit.evalSteps [false, true] 1 = some [false] := by decide
example : firstBit.evalSteps [] 1 = some [false] := by decide
/-- Not halted before the first step. -/
example : firstBit.evalSteps [true] 0 = none := by decide
/-- A result stays the result under a larger clock. -/
example : firstBit.evalSteps [true] 5 = some [true] :=
  firstBit.evalSteps_mono (x := [true]) (by decide) (by decide : 1 ≤ 5)

/-- The decoded machine computes the first bit. -/
example : firstBit.toTM.Computes [true, false] [true] :=
  (firstBit.computes_iff_exists_evalSteps _ _).mpr ⟨1, by decide⟩

/-- The decoded machine runs in time `1` on `[false]`, and it has no other output. -/
example : firstBit.toTM.RunsInTime [false] 1 ∧ ¬firstBit.toTM.Computes [false] [true] := by
  refine ⟨(firstBit.isSome_evalSteps_iff_runsInTime _ _).mp (by decide), fun h ↦ ?_⟩
  have h' : firstBit.toTM.Computes [false] [false] :=
    (firstBit.computes_iff_exists_evalSteps _ _).mpr ⟨1, by decide⟩
  exact absurd (computes_unique h h') (by decide)

/-- The states of `firstBit` are just the initial state. -/
example : firstBit.states = {0} := by decide

/-! ### One work tape -/

/-- Blank work tape. -/
def blank1 : Fin 1 → Option Bool := fun _ ↦ none

/-- Read `b` on the work tape. -/
def sym1 (b : Bool) : Fin 1 → Option Bool := fun _ ↦ some b

/-- The code that copies its input onto the work tape (state `0`), steps back one cell when the
input is exhausted (entering state `1`), and from state `1` outputs the bit under the work head
while halting; on the empty input that cell is blank, a missing key, so it halts with no
output. -/
def lastBit : Code 1 :=
  ⟨[((0, some true, blank1), ⟨2, fun _ ↦ (some (some true), 2), none, some 0⟩),
    ((0, some false, blank1), ⟨2, fun _ ↦ (some (some false), 2), none, some 0⟩),
    ((0, none, blank1), ⟨1, fun _ ↦ (none, 0), none, some 1⟩),
    ((1, none, sym1 true), ⟨1, fun _ ↦ (none, 1), some true, none⟩),
    ((1, none, sym1 false), ⟨1, fun _ ↦ (none, 1), some false, none⟩)]⟩

example : lastBit.evalSteps [true, false, true] 5 = some [true] := by decide
example : lastBit.evalSteps [false, false, true, false] 6 = some [false] := by decide
example : lastBit.evalSteps [] 2 = some [] := by decide
/-- Still copying after three steps on a three-bit input. -/
example : lastBit.evalSteps [true, false, true] 3 = none := by decide

example : lastBit.toTM.Computes [true, true, false] [false] :=
  (lastBit.computes_iff_exists_evalSteps _ _).mpr ⟨5, by decide⟩

example : lastBit.states = {0, 1} := by decide

/-- Every state that a run of `lastBit` enters is `0` or `1`. -/
example (x : List Bool) (t q : ℕ)
    (h : (lastBit.toTM.runFrom (lastBit.toTM.initCfg x) t).state = some q) : q ≤ 1 := by
  have := lastBit.state_runFrom_mem_states x t h
  have hs : lastBit.states = {0, 1} := by decide
  rw [hs] at this
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  omega

/-! ### Coding by numbers and primitive recursiveness -/

example : Code.decode (Code.encode lastBit) = some lastBit := Code.decode_encode _

example : Primrec fun p : Code 1 × List Bool × ℕ ↦ p.1.evalSteps p.2.1 p.2.2 :=
  Code.primrec_evalSteps

/-- With the code fixed, the evaluator is primitive recursive in the input and the clock. -/
example : Primrec fun p : List Bool × ℕ ↦ lastBit.evalSteps p.1 p.2 :=
  Code.primrec_evalSteps.comp ((Primrec.const lastBit).pair Primrec.id)

end CSLibExtTest.Computability.Machines.Turing.MultiTape
