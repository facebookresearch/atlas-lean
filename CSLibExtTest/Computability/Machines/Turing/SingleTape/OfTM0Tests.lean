/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Machines.Turing.SingleTape.OfTM0
public meta import CSLibExt.Computability.Machines.Turing.SingleTape.OfTM0

@[expose] public section

/-!
# Tests for running `TM0` machines on single-tape machines

`bump` is a three-state `TM0` machine over `Fin 3`, with blank `0`: on a word starting with `1`
it steps right and back left, overwrites the `1` with `2`, and halts on the `2`. The runs of its
translation `bumpTM` are compared with those of `bump` cell by cell, and `outputs_ofTM0`,
`outputsWithinTime_ofTM0` and `haltsOn_ofTM0_iff` are applied to `bump` and to `drift`, a machine
that never halts.
-/

set_option autoImplicit false

open Relation StateTransition Turing Cslib.Turing Cslib.Turing.SingleTapeTM

namespace CSLibExtTest.Computability.Machines.Turing.SingleTape.OfTM0

/-- The non-blank symbol `1`. -/
def one : NonBlank (Fin 3) := ⟨1, by decide⟩

/-- The non-blank symbol `2`. -/
def two : NonBlank (Fin 3) := ⟨2, by decide⟩

local instance : Inhabited (NonBlank (Fin 3)) := ⟨one⟩

/-- In state `0` on a `1`, move right into state `1`; in state `1`, move left into state `2`; in
state `2` on a `1`, write `2`; halt otherwise. -/
def bump : TM0.Machine (Fin 3) (Fin 3) := fun q a ↦
  if q = 0 ∧ a = 1 then some (1, .move .right)
  else if q = 1 then some (2, .move .left)
  else if q = 2 ∧ a = 1 then some (2, .write 2)
  else none

/-- All states support `bump`. -/
theorem bump_supports : TM0.Supports bump ↑(Finset.univ : Finset (Fin 3)) := by
  rw [Finset.coe_univ]
  exact TM0.univ_supports bump

/-- The single-tape machine running `bump`. -/
abbrev bumpTM : SingleTapeTM (NonBlank (Fin 3)) := ofTM0 bump Finset.univ bump_supports

/-- Run a single-tape machine for `k` steps, or until it halts. -/
def run {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] (tm : SingleTapeTM Symbol) :
    ℕ → tm.Cfg → tm.Cfg
  | 0, c => c
  | k + 1, c => (tm.step c).elim c (run tm k)

/-- Run `bump` for `k` steps, or until it halts. -/
def runTM0 : ℕ → TM0.Cfg (Fin 3) (Fin 3) → TM0.Cfg (Fin 3) (Fin 3)
  | 0, c => c
  | k + 1, c => (TM0.step bump c).elim c (runTM0 k)

/-- The cells `-3, …, 3` of a tape, counted from the head. -/
def window (T : Tape (Fin 3)) : List (Fin 3) := [-3, -2, -1, 0, 1, 2, 3].map T.nth

/-- The state (`none` once halted) and the cells around the head after `k` steps of `bumpTM` on
`l`. -/
def obs (l : List (NonBlank (Fin 3))) (k : ℕ) : Option (Fin 3) × List (Fin 3) :=
  let c := run bumpTM k (bumpTM.initCfg l)
  (c.state.map Subtype.val, window (toTape c.BiTape))

/-- The state and the cells around the head after `k` steps of `bump` on `l`. -/
def obsTM0 (l : List (Fin 3)) (k : ℕ) : Option (Fin 3) × List (Fin 3) :=
  let c := runTM0 k (TM0.init l)
  (some c.q, window c.Tape)

/-! On `1 1`, `bump` takes three steps and then halts; `bumpTM` takes the same three steps and a
fourth into its halting state, and leaves `2 1`. -/

#guard (List.range 5).map (obs [one, one]) =
  [(some 0, [0, 0, 0, 1, 1, 0, 0]), (some 1, [0, 0, 1, 1, 0, 0, 0]),
    (some 2, [0, 0, 0, 1, 1, 0, 0]), (some 2, [0, 0, 0, 2, 1, 0, 0]),
    (none, [0, 0, 0, 2, 1, 0, 0])]

#guard (List.range 4).all fun k ↦ obs [one, one] k == obsTM0 [1, 1] k

#guard (TM0.step bump (runTM0 3 (TM0.init [1, 1]))).isNone

#guard obs [one, one] 4 == (none, window (Tape.mk₁ [2, 1]))

/-! On `1`, the step right reads a blank. -/

#guard (List.range 4).all fun k ↦ obs [one] k == obsTM0 [1] k

#guard (TM0.step bump (runTM0 3 (TM0.init [1]))).isNone

#guard obs [one] 4 == (none, window (Tape.mk₁ [2]))

/-! On `2` and on the empty word, `bump` halts at once and `bumpTM` halts in one step. -/

#guard obs [two] 0 == obsTM0 [2] 0 && (TM0.step bump (TM0.init [2])).isNone

#guard obs [two] 1 == (none, window (Tape.mk₁ [2]))

#guard obs [] 0 == obsTM0 [] 0 && (TM0.step bump (TM0.init [])).isNone

#guard obs [] 1 == (none, window (Tape.mk₁ []))

/-- The halting step on `2` leaves the tape as it is. -/
example : bumpTM.step (bumpTM.initCfg [two]) = some (bumpTM.haltCfg [two]) := rfl

/-- `bump` halts on `1 1` after three steps, with `2 1` on its tape. -/
theorem bump_eval : (⟨2, Tape.mk₁ [2, 1]⟩ : TM0.Cfg (Fin 3) (Fin 3)) ∈
    eval (TM0.step bump) (TM0.init [1, 1]) :=
  mem_eval.2 ⟨.head rfl (.head rfl (.single rfl)), rfl⟩

/-- So `bumpTM` outputs `2 1` on `1 1`. -/
example : bumpTM.Outputs [one, one] [two, one] :=
  outputs_ofTM0 bump Finset.univ bump_supports bump_eval rfl

/-- `bump` takes three steps on `1 1`, so `bumpTM` takes at most four. -/
example : bumpTM.OutputsWithinTime [one, one] [two, one] 4 :=
  outputsWithinTime_ofTM0 bump Finset.univ bump_supports (c := ⟨2, Tape.mk₁ [2, 1]⟩)
    (.tail _ _ _ _ (.tail _ _ _ _ (.single rfl) rfl) rfl) rfl rfl

/-- `bumpTM` halts on `1 1`, through `haltsOn_ofTM0_iff`. -/
example : bumpTM.HaltsOn [one, one] :=
  (haltsOn_ofTM0_iff bump Finset.univ bump_supports _).2 <|
    Part.dom_iff_mem.2 ⟨_, Part.mem_map _ bump_eval⟩

/-- Move right forever. -/
def drift : TM0.Machine (Fin 3) (Fin 3) := fun _ _ ↦ some (0, .move .right)

/-- All states support `drift`. -/
theorem drift_supports : TM0.Supports drift ↑(Finset.univ : Finset (Fin 3)) := by
  rw [Finset.coe_univ]
  exact TM0.univ_supports drift

/-- `drift` halts on no input, so neither does the machine running it. -/
example (l : List (NonBlank (Fin 3))) :
    ¬(ofTM0 drift Finset.univ drift_supports).HaltsOn l := by
  rw [haltsOn_ofTM0_iff]
  intro h
  obtain ⟨_, hc⟩ := Part.dom_iff_mem.1 h
  obtain ⟨⟨q, T⟩, hc, -⟩ := (Part.mem_map_iff _).1 hc
  have := (mem_eval.1 hc).2
  simp [TM0.step, drift] at this

/-! A machine that writes a blank and then steps left off its input: the two tape cases where a
blank meets the end of a `StackTape` (`cons none nil = nil`). -/

/-- In state `0`, write the blank and go to state `1`; in state `1`, move left into state `2`;
halt in state `2`. -/
def wipe : TM0.Machine (Fin 3) (Fin 3) := fun q _ ↦
  if q = 0 then some (1, .write 0)
  else if q = 1 then some (2, .move .left)
  else none

/-- All states support `wipe`. -/
theorem wipe_supports : TM0.Supports wipe ↑(Finset.univ : Finset (Fin 3)) := by
  rw [Finset.coe_univ]
  exact TM0.univ_supports wipe

/-- The single-tape machine running `wipe`. -/
abbrev wipeTM : SingleTapeTM (NonBlank (Fin 3)) := ofTM0 wipe Finset.univ wipe_supports

/-- Run `wipe` for `k` steps, or until it halts. -/
def runWipe : ℕ → TM0.Cfg (Fin 3) (Fin 3) → TM0.Cfg (Fin 3) (Fin 3)
  | 0, c => c
  | k + 1, c => (TM0.step wipe c).elim c (runWipe k)

/-- The state and the cells around the head after `k` steps of `wipeTM` on `l`. -/
def obsWipe (l : List (NonBlank (Fin 3))) (k : ℕ) : Option (Fin 3) × List (Fin 3) :=
  let c := run wipeTM k (wipeTM.initCfg l)
  (c.state.map Subtype.val, window (toTape c.BiTape))

/-- The state and the cells around the head after `k` steps of `wipe` on `l`. -/
def obsWipeTM0 (l : List (Fin 3)) (k : ℕ) : Option (Fin 3) × List (Fin 3) :=
  let c := runWipe k (TM0.init l)
  (some c.q, window c.Tape)

/-! On `1` the machine blanks the only cell and steps left: the tape is all blank. On `1 2` the
step left pushes the blank cell onto a nonempty right side. -/

#guard (List.range 3).all fun k ↦ obsWipe [one] k == obsWipeTM0 [1] k

#guard obsWipe [one] 3 == (none, [0, 0, 0, 0, 0, 0, 0])

#guard (List.range 3).all fun k ↦ obsWipe [one, two] k == obsWipeTM0 [1, 2] k

#guard obsWipe [one, two] 3 == (none, [0, 0, 0, 0, 0, 2, 0])

end CSLibExtTest.Computability.Machines.Turing.SingleTape.OfTM0
