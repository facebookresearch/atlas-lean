/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.LTL.LanguageInclusion

/-!
# Tests for LTL model checking as language inclusion

Two initial self-loops labelled differently: `G p` fails on the system (the word `false^ω`
is a run outside the formula's language), and holds once the initial set is restricted to
the satisfying loop.
-/

@[expose] public section

namespace Cslib.LTL.LanguageInclusionTests

open Automata.NA Automata.ωAcceptor ModelChecking

/-- Two self-loops. -/
def loops : LTS Bool Unit where
  Tr s _ t := s = t

/-- The atom `0` holds exactly in state `true`. -/
def loopVal (s : Bool) (a : ℕ) : Prop := s = true ∧ a = 0

/-- The run `false^ω` is accepted by the system automaton. -/
theorem const_false_mem :
    ωSequence.const false ∈ language (systemAutomaton loops Set.univ) :=
  (mem_systemAutomaton_iff loops Set.univ _).mpr ⟨trivial, ωSequence.const (), fun _ => rfl⟩

/-- Inclusion fails, so `G p` is not satisfied from both states. -/
example : ¬ language (systemAutomaton loops Set.univ) ≤
    language (Tableau.buchi loopVal (Formula.always (.atom 0))) := by
  intro h
  have := (Tableau.mem_buchi_iff loopVal _ _).mp (h const_false_mem)
  rw [Word.Satisfies.always_iff] at this
  simpa [Word.satisfiesAt_atom, loopVal] using this 0

/-- From `true` alone, `G p` holds, hence inclusion and empty intersection. -/
theorem models_true : Models loops {true} loopVal (Formula.always (.atom 0)) := by
  intro w
  rintro ⟨hstart, actions, hexec⟩
  have hall : ∀ n, w n = true := by
    intro n
    induction n with
    | zero => exact hstart
    | succ n ih => exact (hexec n).symm.trans ih
  rw [Word.Satisfies.always_iff]
  intro n
  simp [Word.satisfiesAt_atom, loopVal, hall n]

example : language (systemAutomaton loops {true}) ≤
    language (Tableau.buchi loopVal (Formula.always (.atom 0))) :=
  (models_iff_language_le _ _ _ _).mp models_true

example : language (systemAutomaton loops {true}) ⊓
    language (Tableau.buchi loopVal (.not (Formula.always (.atom 0)))) = ⊥ :=
  (models_iff_inf_language_neg_eq_bot _ _ _ _).mp models_true

end Cslib.LTL.LanguageInclusionTests
