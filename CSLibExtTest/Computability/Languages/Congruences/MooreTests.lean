/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.Congruences.Moore

/-!
# Tests for Moore's minimization algorithm

* `parity4` counts `true`s modulo 4 and accepts counts `0` and `2`: states `0, 2` and `1, 3` are
  equivalent, so Moore's automaton has two states.
* `withDead` has states `0, 1` for the parity of `true`s and an unreachable accepting state `2`:
  the unreachable state is dropped, leaving two states. State `2` accepts every word, so it is
  related to neither `0` nor `1`.
* Larger inputs, which stop early: counting `true`s modulo 8 and accepting even counts
  minimizes to two states; a 12-state automaton that accepts everything and never moves
  minimizes to one state after a single refinement round; with a budget of a million rounds
  the iteration still returns at once.
* The quotient accepts the original language and equals the semantic minimal automaton after
  renaming (`reindex_mooreDFA`).
-/

@[expose] public section

namespace DFA.MooreTests

/-- Number of `true`s modulo 4; accept counts `0` and `2`. -/
def parity4 : DFA Bool (Fin 4) := ⟨fun s b => if b then s + 1 else s, 0, {0, 2}⟩

instance : DecidablePred (· ∈ parity4.accept) :=
  inferInstanceAs (DecidablePred (· ∈ ({0, 2} : Set (Fin 4))))

example : ((0 : Fin 4), (2 : Fin 4)) ∈ parity4.mooreRel := by decide +kernel
example : ((0 : Fin 4), (1 : Fin 4)) ∉ parity4.mooreRel := by decide +kernel
example : Fintype.card parity4.MooreState = 2 := by decide +kernel

/-- Parity of `true`s on states `0, 1`, plus an unreachable accepting state `2`. -/
def withDead : DFA Bool (Fin 3) :=
  ⟨fun s b => if s = 2 then 2 else if b then 1 - s else s, 0, {0, 2}⟩

instance : DecidablePred (· ∈ withDead.accept) :=
  inferInstanceAs (DecidablePred (· ∈ ({0, 2} : Set (Fin 3))))

example : Fintype.card withDead.MooreState = 2 := by decide +kernel
example : ((0 : Fin 3), (2 : Fin 3)) ∉ withDead.mooreRel := by decide +kernel
example : ((1 : Fin 3), (2 : Fin 3)) ∉ withDead.mooreRel := by decide +kernel

/-- Number of `true`s modulo 8; accept even counts. -/
def parity8 : DFA Bool (Fin 8) := ⟨fun s b => if b then s + 1 else s, 0, {s | s.val % 2 = 0}⟩

instance : DecidablePred (· ∈ parity8.accept) :=
  inferInstanceAs (DecidablePred fun s : Fin 8 => s.val % 2 = 0)

example : Fintype.card parity8.MooreState = 2 := by decide +kernel

/-- Twelve states, all accepting, no moves. -/
def still12 : DFA Bool (Fin 12) := ⟨fun s _ => s, 0, Set.univ⟩

instance : DecidablePred (· ∈ still12.accept) :=
  inferInstanceAs (DecidablePred (· ∈ (Set.univ : Set (Fin 12))))

example : still12.mooreRel = Finset.univ := by decide +kernel

/-- Early stopping: with a budget of a million rounds the iteration still returns after one
round, since the first round changes nothing (without the stop this would not finish). -/
example : still12.mooreIter 1000000 Finset.univ = Finset.univ := by decide +kernel
example : Fintype.card still12.MooreState = 1 := by decide +kernel

example : parity4.mooreDFA.accepts = parity4.accepts := parity4.mooreDFA_accepts

example :
    DFA.reindex parity4.mooreEquiv parity4.mooreDFA = Cslib.Language.minimizedDFA parity4 :=
  parity4.reindex_mooreDFA

end DFA.MooreTests
