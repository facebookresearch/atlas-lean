/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Nondeterministic parity automata
-/
module

public import Cslib.Computability.Automata.NA.Basic
public import CSLibExt.Foundations.Data.OmegaSequence.Parity

/-!
# Nondeterministic parity automata

A nondeterministic parity automaton extends upstream CSLib's `Cslib.Automata.NA` (and so the
upstream `Cslib.LTS`) with a priority for each state. A run is accepting under the max-parity
condition `Cslib.ωSequence.ParityEven`: the largest priority visited infinitely often exists and
is even. With infinitely many states and unbounded priorities that largest priority may not exist,
and such runs are rejected; with finitely many states it always exists.

* `Cslib.Automata.NA.Parity` and its `ωAcceptor` instance.
* `Cslib.Automata.NA.Buchi.toParity`: a Büchi automaton is the parity automaton with priority `2`
  on accepting states and `1` elsewhere, accepting the same language
  (`Cslib.Automata.NA.Buchi.language_toParity`).
* `Cslib.Automata.NA.Parity.run_parityEven_or_parityOdd`: with finitely many states the priorities
  of a run are bounded, so the run is won by exactly one parity.
-/

@[expose] public section

namespace Cslib.Automata.NA

open Filter ωSequence ωAcceptor

variable {State Symbol : Type*}

/-- Nondeterministic parity automaton: a nondeterministic automaton with a priority for each
state. -/
structure Parity (State Symbol : Type*) extends NA State Symbol where
  /-- The priority of each state. -/
  priority : State → ℕ

namespace Parity

/-- An infinite run is accepting iff the largest priority it visits infinitely often is even. -/
@[simp]
instance : ωAcceptor (Parity State Symbol) Symbol where
  Accepts (a : Parity State Symbol) (xs : ωSequence Symbol) :=
    ∃ ss, a.Run xs ss ∧ ParityEven (ss.map a.priority)

theorem mem_language_iff {a : Parity State Symbol} {xs : ωSequence Symbol} :
    xs ∈ language a ↔ ∃ ss, a.Run xs ss ∧ ParityEven (ss.map a.priority) :=
  Iff.rfl

/-- With finitely many states, every run is won by the even or by the odd parity (and never by
both, `Cslib.ωSequence.not_parityEven_and_parityOdd`). -/
theorem run_parityEven_or_parityOdd [Finite State] (a : Parity State Symbol)
    (ss : ωSequence State) : ParityEven (ss.map a.priority) ∨ ParityOdd (ss.map a.priority) := by
  obtain ⟨d, hd⟩ := (Set.finite_range a.priority).bddAbove
  exact parityEven_or_parityOdd (d := d) fun k => hd ⟨ss k, rfl⟩

end Parity

namespace Buchi

/-- A Büchi automaton as a parity automaton: priority `2` on accepting states, `1` elsewhere. -/
def toParity (na : Buchi State Symbol) [DecidablePred (· ∈ na.accept)] : Parity State Symbol where
  toNA := na.toNA
  priority s := if s ∈ na.accept then 2 else 1

/-- A Büchi automaton and its parity presentation accept the same language. -/
theorem language_toParity (na : Buchi State Symbol) [DecidablePred (· ∈ na.accept)] :
    language na.toParity = language na := by
  apply ωLanguage.mem_ext
  intro xs
  rw [Parity.mem_language_iff, mem_language]
  refine exists_congr fun ss => and_congr Iff.rfl ?_
  have hps : ∀ k, (ss.map na.toParity.priority) k = 1 ∨ (ss.map na.toParity.priority) k = 2 :=
    fun k => by
      simp only [get_map, toParity]
      split_ifs <;> simp
  rw [parityEven_iff_frequently_two hps]
  refine frequently_congr (Eventually.of_forall fun k => ?_)
  simp only [get_map, toParity]
  split_ifs with h <;> simp [h]

end Buchi

end Cslib.Automata.NA
