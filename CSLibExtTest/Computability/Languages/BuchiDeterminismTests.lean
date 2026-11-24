/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.BuchiDeterminism

/-!
# Tests for the separation of nondeterministic and deterministic Büchi automata

The two-state nondeterministic automaton accepts `0^ω` and rejects `1^ω`, so the separated
language is neither empty nor universal.
-/

@[expose] public section

namespace Cslib.BuchiDeterminismTests

open Automata Automata.ωAcceptor ωLanguage.Example Filter

example : ωSequence.const (0 : Fin 2) ∈ language eventuallyZeroNa := by
  rw [eventuallyZero_accepted_by_na_buchi]
  exact Eventually.of_forall fun _ => rfl

example : ωSequence.const (1 : Fin 2) ∉ language eventuallyZeroNa := by
  rw [eventuallyZero_accepted_by_na_buchi]
  intro h
  obtain ⟨k, hk⟩ := h.exists
  exact absurd hk (by simp)

example : ¬ ∃ (State : Type) (da : DA.Buchi State (Fin 2)), language da = eventuallyZero :=
  nondeterministic_buchi_strictly_more_expressive.2.2

end Cslib.BuchiDeterminismTests
