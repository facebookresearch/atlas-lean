/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.Congruences.Brzozowski

/-!
# Tests for Brzozowski's minimization algorithm

* `parity4` counts `true`s modulo 4 and accepts counts `0` and `2`: the reversed language is the
  same parity language, so both determinized reversals have two reachable subsets, and
  Brzozowski's automaton has two states.
* `withDead` adds an unreachable accepting state to the parity automaton: it disappears, leaving
  two states.
* `endsTrue` accepts the words ending in `true`, with a redundant third state; its reversal (the
  words starting with `true`) needs three states including a dead one, and the result again has
  two states.
* `fourthTrue` (the fourth letter is `true`, six states) has a reversal with 16 reachable
  subsets; Brzozowski's automaton has six states, found without enumerating all `2 ^ 16` subsets
  of the intermediate states. The `Fintype` instances of both state types are
  `Finset.Subtype.fintype`, which lists the computed reachable finset.
* The result accepts the original language and equals the semantic minimal automaton after
  renaming (`reindex_brzozowski`).
-/

@[expose] public section

namespace DFA.BrzozowskiTests

/-- Number of `true`s modulo 4; accept counts `0` and `2`. -/
def parity4 : DFA Bool (Fin 4) := ⟨fun s b => if b then s + 1 else s, 0, {0, 2}⟩

instance : DecidablePred (· ∈ parity4.accept) :=
  inferInstanceAs (DecidablePred (· ∈ ({0, 2} : Set (Fin 4))))

example : Fintype.card parity4.MidState = 2 := by decide +kernel
example : Fintype.card parity4.BrzozowskiState = 2 := by decide +kernel

/-- Parity of `true`s on states `0, 1`, plus an unreachable accepting state `2`. -/
def withDead : DFA Bool (Fin 3) :=
  ⟨fun s b => if s = 2 then 2 else if b then 1 - s else s, 0, {0, 2}⟩

instance : DecidablePred (· ∈ withDead.accept) :=
  inferInstanceAs (DecidablePred (· ∈ ({0, 2} : Set (Fin 3))))

example : Fintype.card withDead.BrzozowskiState = 2 := by decide +kernel

/-- The last letter read, with two copies (`1`, `2`) of the state "last letter was `true`". -/
def endsTrue : DFA Bool (Fin 3) :=
  ⟨fun s b => if b then (if s = 1 then 2 else 1) else 0, 0, {1, 2}⟩

instance : DecidablePred (· ∈ endsTrue.accept) :=
  inferInstanceAs (DecidablePred (· ∈ ({1, 2} : Set (Fin 3))))

example : Fintype.card endsTrue.MidState = 3 := by decide +kernel
example : Fintype.card endsTrue.BrzozowskiState = 2 := by decide +kernel

example : [false, true] ∈ endsTrue.brzozowski.accepts := by
  rw [brzozowski_accepts, mem_accepts]
  decide
example : [true, false] ∉ endsTrue.brzozowski.accepts := by
  rw [brzozowski_accepts, mem_accepts]
  decide

/-- The fourth letter is `true`: positions `0` to `3`, an accepting sink `4` and a rejecting
sink `5`. -/
def fourthTrue : DFA Bool (Fin 6) :=
  ⟨fun s b => if s.val < 3 then s + 1 else if s.val = 3 then (if b then 4 else 5) else s, 0, {4}⟩

instance : DecidablePred (· ∈ fourthTrue.accept) :=
  inferInstanceAs (DecidablePred (· ∈ ({4} : Set (Fin 6))))

/-- The reversal (the fourth letter from the end is `true`) needs `2 ^ 4` subsets; the second
determinization then ranges over subsets of those 16 states, and the early-stopping search
finds the 6 reachable ones without visiting the `2 ^ 16` candidates. -/
example : Fintype.card fourthTrue.MidState = 16 := by decide +kernel
example : Fintype.card fourthTrue.BrzozowskiState = 6 := by decide +kernel

/-- The state types enumerate the computed reachable finsets (`Finset.Subtype.fintype`, i.e.
`Finset.attach`), not the ambient type of all subsets filtered by membership. -/
example : (inferInstance : Fintype fourthTrue.MidState) = Finset.Subtype.fintype _ := rfl
example : (inferInstance : Fintype fourthTrue.BrzozowskiState) = Finset.Subtype.fintype _ := rfl

example : parity4.brzozowski.accepts = parity4.accepts := parity4.brzozowski_accepts

example :
    DFA.reindex parity4.brzozowskiEquiv parity4.brzozowski = Cslib.Language.minimizedDFA parity4 :=
  parity4.reindex_brzozowski

end DFA.BrzozowskiTests
