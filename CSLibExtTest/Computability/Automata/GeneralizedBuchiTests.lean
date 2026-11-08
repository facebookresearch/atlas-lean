/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Tests for generalized Büchi automata and degeneralization
-/
module

public import CSLibExt.Computability.Automata.NA.GeneralizedBuchi

/-!
# Tests for generalized Büchi automata and degeneralization

A two-set generalized Büchi automaton on one state with all transitions
present: the constant-`true` word is accepted by the degeneralized automaton,
via `language_toBuchi`, and the counter advances through both acceptance sets.
-/

@[expose] public section

namespace Cslib.Automata.NA.GenBuchi.Tests

open ωSequence ωAcceptor

/-- One state, all transitions present, two acceptance sets both equal `{true}`. -/
def twoSet : GenBuchi Bool Bool where
  Tr _ _ _ := True
  start := {true}
  k := 2
  accept _ := {true}

/-- The counter advances from `0` to `1` on landing in the first set. -/
example : twoSet.nextCount ⟨0, by decide⟩ true = ⟨1, by decide⟩ :=
  GenBuchi.nextCount_eq_succ (by decide) rfl

/-- The counter resets from `2` to `0`. -/
example : twoSet.nextCount ⟨2, by decide⟩ true = ⟨0, by decide⟩ :=
  GenBuchi.nextCount_eq_zero rfl

/-- The constant-`true` word is accepted by the degeneralized automaton. -/
example : ωSequence.const true ∈ language twoSet.toBuchi := by
  rw [GenBuchi.language_toBuchi]
  refine ⟨ωSequence.const true, ⟨rfl, fun _ => trivial⟩, fun _ => ?_⟩
  exact Filter.Frequently.of_forall (fun _ => rfl)

end Cslib.Automata.NA.GenBuchi.Tests
