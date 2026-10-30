/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Machines.Turing.MultiTape.Basic

@[expose] public section

/-!
# Tests for the basic multi-tape API

`firstBitTM`, a machine of CSLib's multi-tape model with no work tapes and one state, outputs
whether its first input bit is `true` and halts in one step. Its runs are computed through
`runFrom_ofTr`, and the halting and output lemmas are applied to them.
-/

set_option autoImplicit false

open Cslib.Turing.MultiTapeTM _root_.Turing

namespace CSLibExtTest.Computability.Machines.Turing.MultiTape

/-- Output whether the first input bit is `true`, and halt. -/
noncomputable def firstBitTM : MultiTapeTM 0 Bool Unit :=
  MultiTapeTM.ofTr () fun _ a _ ↦ ⟨0, Fin.elim0, some (a == some true), none⟩

/-- After one step `firstBitTM` has halted, with output `[w.head? == some true]`. -/
theorem firstBitTM_runFrom_one (w : List Bool) :
    (firstBitTM.runFrom (firstBitTM.initCfg w) 1).Halted ∧
      (firstBitTM.runFrom (firstBitTM.initCfg w) 1).output = [w.head? == some true] := by
  unfold firstBitTM
  rw [runFrom_ofTr]
  cases w with
  | nil =>
    have h : (Cfg.init (k := 0) (State := Unit) () ([] : List Bool)).inputSymbol = none :=
      inputSymbol_eq_none_of_boundary (Or.inr rfl)
    simp only [Cfg.init] at h
    simp [stepWith, h, Cfg.Halted, Action.apply_state]
  | cons b w => simp [stepWith, Cfg.Halted, Action.apply_state]

/-- The run of `firstBitTM` halts at exactly step `1`. -/
example (w : List Bool) : firstBitTM.HaltsAt (firstBitTM.initCfg w) 1 :=
  haltsAt_add (m := 1) (n := 0) (fun s hs ↦ by
      obtain rfl : s = 0 := by omega
      simp [firstBitTM])
    (haltsAt_zero_iff.mpr (firstBitTM_runFrom_one w).1)

/-- It runs in time `1`, and its only output on `[true]` is `[true]`. -/
example : firstBitTM.RunsInTime [true] 1 ∧
    ∀ o, firstBitTM.Computes [true] o → o = [true] := by
  have h := firstBitTM_runFrom_one [true]
  refine ⟨runsInTime_iff_halted.mpr h.1, fun o ho ↦ ?_⟩
  exact (computes_unique ho ⟨1, h.1, h.2⟩)

/-- The configuration at the time bound determines the output. -/
example (o : List Bool) :
    firstBitTM.Computes [false, true] o ↔ o = [false] := by
  have h := firstBitTM_runFrom_one [false, true]
  rw [computes_iff_output_of_runsInTime (runsInTime_iff_halted.mpr h.1), h.2]
  exact ⟨fun h ↦ by simpa using h.symm, fun h ↦ by simp [h]⟩

/-- Steps from a configuration agree. -/
example {x : List Bool} {c c₁ c₂ : Cfg 0 Bool Unit x} (h₁ : firstBitTM.Step c c₁)
    (h₂ : firstBitTM.Step c c₂) : c₁ = c₂ :=
  step_deterministic h₁ h₂

end CSLibExtTest.Computability.Machines.Turing.MultiTape
