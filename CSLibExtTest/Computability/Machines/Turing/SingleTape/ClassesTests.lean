/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Machines.Turing.SingleTape.Classes

@[expose] public section

/-!
# Tests for the single-tape decidable and recognizable classes

Small machines in each class: a one-step decider on `Unit`, a machine that halts at once (it
recognizes the always-true predicate on `ℕ`), a machine that never halts (it recognizes the
always-false predicate), and the degenerate decider that injectivity of the input copy rules out.
-/

set_option autoImplicit false

open Relation Computability Cslib.Turing Cslib.Decidability

namespace CSLibExtTest.Computability.Machines.Turing.SingleTape

/-- Write `true` under the head and halt. -/
def writeTrue : SingleTapeTM Bool where
  State := Unit
  q₀ := ()
  tr _ _ := (⟨some true, none⟩, none)

/-- Halt at once, leaving the tape unchanged. -/
def haltNow : SingleTapeTM Bool where
  State := Unit
  q₀ := ()
  tr _ s := (⟨s, none⟩, none)

/-- Never halt: stay in the same state without touching the tape. -/
def loopForever : SingleTapeTM Bool where
  State := Unit
  q₀ := ()
  tr _ s := (⟨s, none⟩, some ())

/-- `Unit` has the single code `0`, so its input word is empty, and `writeTrue` outputs `[true]`
on it: the always-true predicate on `Unit` is decidable. -/
example : SingleTapeDecidable fun _ : Unit ↦ True :=
  ⟨Bool, inferInstance, inferInstance, id, Function.injective_id, writeTrue, fun _ ↦
    ⟨true, ReflTransGen.single rfl, by simp⟩⟩

/-- `haltNow` halts on every input. -/
theorem haltNow_haltsOn (l : List Bool) : haltNow.HaltsOn l :=
  ⟨_, ReflTransGen.single rfl, rfl⟩

example : SingleTapeRecognizable fun _ : ℕ ↦ True :=
  ⟨Bool, inferInstance, inferInstance, id, Function.injective_id, haltNow, fun _ ↦
    iff_of_true (haltNow_haltsOn _) trivial⟩

/-- Every configuration `loopForever` reaches from a running one is running. -/
theorem loopForever_isSome {c c' : loopForever.Cfg} (hc : c.state.isSome)
    (h : ReflTransGen loopForever.TransitionRelation c c') : c'.state.isSome := by
  induction h with
  | refl => exact hc
  | tail _ hstep ih =>
    rename_i b d _
    obtain ⟨s, t⟩ := b
    cases s with
    | none => simp at ih
    | some q =>
      simp only [SingleTapeTM.TransitionRelation, SingleTapeTM.step, loopForever] at hstep
      rw [← Option.some_injective _ hstep]
      rfl

/-- `loopForever` halts on no input. -/
theorem not_loopForever_haltsOn (l : List Bool) : ¬loopForever.HaltsOn l := by
  rintro ⟨c, h, hc⟩
  have := loopForever_isSome (c := loopForever.initCfg l) rfl h
  rw [hc] at this
  cases this

example : SingleTapeRecognizable fun _ : ℕ ↦ False :=
  ⟨Bool, inferInstance, inferInstance, id, Function.injective_id, loopForever, fun _ ↦
    iff_of_false (not_loopForever_haltsOn _) id⟩

/-- A decider's answer is meaningful only with an injective input copy: with the constant
`ι := fun _ ↦ true`, the decider for `True` above also "decides" `False` (answer `b = false`,
written `ι false = true`). -/
example : ∀ a : Unit, ∃ b : Bool,
    writeTrue.Outputs ((encodeNat (Encodable.encode a)).map fun _ ↦ true) [(fun _ ↦ true) b] ∧
      (b = true ↔ False) := fun _ ↦
  ⟨false, ReflTransGen.single rfl, by simp⟩

/-- The constant copy is not injective, so `SingleTapeDecidable` does not accept that witness. -/
example : ¬Function.Injective fun _ : Bool ↦ true := fun h ↦ Bool.false_ne_true (h rfl)

/-- `writeTrue` outputs only `[true]` on the empty input (`Outputs.unique`). -/
example (l : List Bool) (h : writeTrue.Outputs [] l) : l = [true] :=
  h.unique (ReflTransGen.single rfl)

/-! ### Halting from a configuration -/

/-- `haltNow` halts from every running configuration, in one step. -/
theorem haltNow_haltsFrom (t : BiTape Bool) : haltNow.HaltsFrom ⟨some (), t⟩ :=
  ⟨_, ReflTransGen.single rfl, rfl⟩

/-- Halting on an input is halting from the initial configuration. -/
example (l : List Bool) : haltNow.HaltsOn l :=
  SingleTapeTM.haltsOn_iff_haltsFrom.mpr (haltNow_haltsFrom _)

/-- `loopForever` halts from no configuration reachable from an initial one: halting from such a
configuration would give halting from the initial configuration, backwards along the run. -/
example (l : List Bool) (c : loopForever.Cfg)
    (hc : ReflTransGen loopForever.TransitionRelation (loopForever.initCfg l) c) :
    ¬loopForever.HaltsFrom c := fun h ↦
  not_loopForever_haltsOn l ((SingleTapeTM.haltsFrom_iff_of_reflTransGen hc).mpr h)

/-- Every configuration on a halting run halts, forwards along the run. -/
example (l : List Bool) (c : haltNow.Cfg)
    (hc : ReflTransGen haltNow.TransitionRelation (haltNow.initCfg l) c) : haltNow.HaltsFrom c :=
  (SingleTapeTM.haltsFrom_iff_of_reflTransGen hc).mp (haltNow_haltsOn l)

/-- `writeTrue` overwrites the head cell, so two tapes that differ only there have the same
successor, and `writeTrue` halts from both or from neither. -/
example (L R : StackTape Bool) :
    writeTrue.HaltsFrom ⟨some (), ⟨some false, L, R⟩⟩ ↔
      writeTrue.HaltsFrom ⟨some (), ⟨none, L, R⟩⟩ :=
  SingleTapeTM.haltsFrom_iff_of_step_eq rfl

/-- Two halted configurations have no successor, and both halt, whatever their tapes. -/
example (t t' : BiTape Bool) : loopForever.HaltsFrom ⟨none, t⟩ ↔ loopForever.HaltsFrom ⟨none, t'⟩ :=
  SingleTapeTM.haltsFrom_iff_of_step_eq rfl

/-- In CSLib's terms, `haltNow` is normalizable from every running configuration, and
`loopForever` from none reachable from an initial one. -/
example (t : BiTape Bool) : Relation.Normalizable haltNow.TransitionRelation ⟨some (), t⟩ :=
  SingleTapeTM.haltsFrom_iff_normalizable.mp (haltNow_haltsFrom t)

example (l : List Bool) :
    ¬Relation.Normalizable loopForever.TransitionRelation (loopForever.initCfg l) := fun h ↦
  not_loopForever_haltsOn l (SingleTapeTM.haltsFrom_iff_normalizable.mpr h)

end CSLibExtTest.Computability.Machines.Turing.SingleTape
