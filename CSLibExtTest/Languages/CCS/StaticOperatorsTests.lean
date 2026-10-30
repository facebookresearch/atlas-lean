/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.CCS.StaticOperators

/-!
# Tests for CCS restriction and relabelling

* Relabelling tables are first-match: with duplicate entries for a channel,
  the earliest entry wins; channels absent from the table keep the identity.
* Relabelling is polarity-sensitive through one shared table: if `0` maps to
  the output `1`, then input `0` becomes output `1` and output `0` becomes
  input `1`; the silent action is never renamed.
* A relabelled process performs the relabelled action.
* Restriction blocks transitions on restricted channels, permits transitions
  on other channels, and always permits silent transitions.
-/

@[expose] public section

namespace Cslib.CCS.StaticOperatorsTests

open Cslib.CCS (Label VisibleLabel Relabelling StaticProcess)

/-- A table with two entries for channel `0`: the first one wins. -/
def duplicateTable : Relabelling (Fin 3) :=
  ⟨[(0, .output 1), (0, .input 2)]⟩

/-- First-match semantics: the second entry for `0` is ignored. -/
example : duplicateTable.apply 0 = .output 1 := by decide

/-- Identity fallback: channels absent from the table map to themselves. -/
example : duplicateTable.apply 2 = .input 2 := by decide

/-- The empty table is the identity relabelling. -/
example : (Relabelling.mk [] : Relabelling (Fin 3)).apply 1 = .input 1 := by decide

/-- Polarity: input `0` takes the table image directly. -/
example : StaticProcess.relabelAction duplicateTable (.input 0) = .output 1 := by decide

/-- Polarity: output `0` takes the complement of the same table image. -/
example : StaticProcess.relabelAction duplicateTable (.output 0) = .input 1 := by decide

/-- The silent action is never renamed. -/
example : StaticProcess.relabelAction duplicateTable (.tau : Label (Fin 3)) = .tau := rfl

/-- A relabelled process performs the relabelled action and stays under the
same relabelling. -/
example :
    StaticProcess.Step (.relabelling duplicateTable (.prefix (.input 0) .nil))
      (.output 1) (.relabelling duplicateTable .nil) :=
  .relabel (.prefix _ _)

/-- Relabelling also applies under the other polarity. -/
example :
    StaticProcess.Step (.relabelling duplicateTable (.prefix (.output 0) .nil))
      (.input 1) (.relabelling duplicateTable .nil) :=
  .relabel (.prefix _ _)

/-- Restriction permits a transition whose channel is not blocked. -/
example :
    StaticProcess.Step (.restriction [0] (.prefix (.input 1) .nil))
      (.input 1) (.restriction [0] .nil) :=
  .restrict (.prefix _ _) (by simp)

/-- Restriction always permits silent transitions. -/
example :
    StaticProcess.Step (.restriction [0] (.prefix .tau .nil))
      .tau (.restriction [0] .nil) :=
  .restrict (.prefix _ _) (by simp)

/-- Restriction blocks every transition on a blocked channel: the process
below has no transitions at all. -/
example (action : Label (Fin 3)) (next : StaticProcess (Fin 3)) :
    ¬ StaticProcess.Step (.restriction [0] (.prefix (.input 0) .nil)) action next := by
  intro h
  obtain ⟨process', hstep, hallowed, -⟩ := StaticProcess.restriction_step_iff.1 h
  obtain ⟨rfl, -⟩ := StaticProcess.prefix_step_iff.1 hstep
  simp at hallowed

end Cslib.CCS.StaticOperatorsTests
