/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Machines.Turing.MultiTape.CodeCompleteness

@[expose] public section

/-!
# Tests for code completeness and state relabelling

`headBit` (no work tapes) outputs the first input bit, or `false` on the empty input, and halts.
Its finite-state machine `headBit.toFinTM` has one state and computes the same outputs in the same
time; the language of words starting with `true` is therefore decidable in time `1` and space `0`
on CSLib's model, and lies in `DTIME 1`. In the other direction, `unitFirstBit`, a machine with
states in `Unit` written directly with `MultiTapeTM.ofTr`, is simulated by the machine of its code
`Code.ofTM`, which computes the same outputs.
-/

set_option autoImplicit false

open Cslib.Turing.MultiTapeTM _root_.Turing

namespace CSLibExtTest.Computability.Machines.Turing.MultiTape.CodeCompleteness

/-! ### From codes to finite-state machines -/

/-- The code that outputs the first input bit (`false` on the empty input) and halts. -/
def headBit : Code 0 :=
  ⟨[((0, some true, Fin.elim0), ⟨1, Fin.elim0, some true, none⟩),
    ((0, some false, Fin.elim0), ⟨1, Fin.elim0, some false, none⟩),
    ((0, none, Fin.elim0), ⟨1, Fin.elim0, some false, none⟩)]⟩

/-- `headBit` has the single state `0`. -/
example : headBit.stateBound = 1 := by decide

/-- The evaluator on symbolic inputs: one step reads the first bit. -/
theorem evalSteps_headBit (w : List Bool) :
    headBit.evalSteps w 1 = some [w.headI] := by
  rcases w with _ | ⟨_ | _, w⟩ <;> rfl

/-- The finite-state machine of `headBit` computes the first bit. -/
example : headBit.toFinTM.Computes [true, false] [true] :=
  headBit.isRelabelling_toFinTM.computes_iff.mp
    ((headBit.computes_iff_exists_evalSteps _ _).mpr ⟨1, by decide⟩)

/-- The words that start with `true`. -/
def startsTrue : Set (List Bool) := {w | w.headI = true}

theorem headBit_decides : Decides headBit.toTM startsTrue := fun w ↦
  (headBit.computes_iff_exists_evalSteps _ _).mpr ⟨1, by
    rw [evalSteps_headBit]
    by_cases h : w.headI = true <;> simp [MultiTapeTM.indicator, startsTrue, h]⟩

theorem headBit_runsInTime (w : List Bool) : headBit.toTM.RunsInTime w 1 :=
  (headBit.isSome_evalSteps_iff_runsInTime _ _).mp (by rw [evalSteps_headBit]; rfl)

/-- A code's resource bounds land in `DecidableInTimeAndSpace`. -/
example : MultiTapeTM.DecidableInTimeAndSpace startsTrue (Function.Embedding.refl _)
    (fun _ ↦ 1) (fun _ ↦ 0) :=
  headBit.decidableInTimeAndSpace headBit_decides headBit_runsInTime
    fun w ↦ MultiTapeNTM.runsInSpace_zero_tapes _ w 0

/-- The same through the class characterization over codes. -/
example : startsTrue ∈ DTIME fun _ ↦ 1 :=
  mem_DTIME_iff_exists_code.mpr ⟨1, 0, 0, headBit, headBit_decides,
    fun w ↦ by simpa using headBit_runsInTime w, fun _ ↦ 0,
    fun w ↦ MultiTapeNTM.runsInSpace_zero_tapes _ w 0⟩

/-! ### From finite-state machines to codes -/

/-- A machine with states in `Unit` that outputs the first input bit (`false` on the empty input)
and halts. -/
noncomputable def unitFirstBit : MultiTapeTM 0 Bool Unit :=
  MultiTapeTM.ofTr () fun _ a _ ↦ ⟨0, Fin.elim0, some (a.getD false), none⟩

theorem unitFirstBit_computes (b : Bool) (w : List Bool) :
    unitFirstBit.Computes (b :: w) [b] := by
  refine ⟨1, ?_, ?_⟩ <;>
  · rw [MultiTapeTM.runFrom_succ, runFrom_zero, unitFirstBit, step_ofTr]
    rfl

/-- The code of `unitFirstBit`, numbering its one state by `0`, computes the same outputs. -/
example (b : Bool) (w : List Bool) :
    (Code.ofTM unitFirstBit fun _ ↦ 0).toTM.Computes (b :: w) [b] :=
  (Code.isRelabelling_ofTM unitFirstBit (fun _ _ _ ↦ rfl) rfl).computes_iff.mpr
    (unitFirstBit_computes b w)

/-- Some code computes what `unitFirstBit` computes. -/
example : ∃ c : Code 0, c.toTM.Computes [true] [true] := by
  obtain ⟨c, e, -, h⟩ := Code.exists_code_isRelabelling unitFirstBit
  exact ⟨c, h.computes_iff.mpr (unitFirstBit_computes true [])⟩

/-- Every machine relabels itself by the identity. -/
example : IsRelabelling id unitFirstBit unitFirstBit := IsRelabelling.refl _

/-- Relabellings compose. -/
example : IsRelabelling ((fun _ ↦ 0 : Unit → ℕ) ∘ id) unitFirstBit
    (Code.ofTM unitFirstBit fun _ ↦ 0).toTM :=
  (IsRelabelling.refl _).trans (Code.isRelabelling_ofTM unitFirstBit (fun _ _ _ ↦ rfl) rfl)

end CSLibExtTest.Computability.Machines.Turing.MultiTape.CodeCompleteness
