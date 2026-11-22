/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Decidability.Regular

/-!
# Tests for the DFA decision procedures

Over the alphabet `Bool`:

* `parity` counts `true`s modulo 2 and accepts an even count; `parity4` counts modulo 4 and
  accepts counts `0` and `2`. They accept the same language, so `equivB` returns `true`, and
  by `equivB_iff` the languages are equal.
* `odd` accepts an odd count: not equivalent to `parity`.
* `deadAccept` has an accepting state that cannot be reached, so its language is empty even
  though its accepting set is not.
* `all` accepts every word: universal; `parity` is not.

Encoded DFAs (`Cslib.Automata.EncodedDFA`), over `Bool`, where reading a letter without a listed
transition stays put:

* `eParity` (parity of `true`s on states `0, 1`) accepts `[true, true]` and rejects `[true]`;
  its reachable states are `0` and `1`.
* `eParity4` (counting `true`s modulo 4, accepting `0, 2`) is equivalent to `eParity`; `eOdd` is
  not; `eDead`, whose only accepting state is unreachable, is empty.
* Universality: an all-accepting encoding is universal, `eParity` is not. Infiniteness:
  `eParity` is infinite; `eOne`, which accepts only `[true]`, is finite.
* Sipser's Theorems 4.1, 4.4 and 4.5, ALL_DFA and INFINITE_DFA as `TM2Decidable` statements
  (4.7 and 4.8 are tested with the grammars, in `ContextFreeTests.lean`).
-/

@[expose] public section

namespace DFA.RegularTests

/-- Number of `true`s modulo 2; accept an even count. -/
def parity : DFA Bool (Fin 2) := ⟨fun s b => if b then s + 1 else s, 0, {0}⟩

/-- Number of `true`s modulo 4; accept counts `0` and `2`. -/
def parity4 : DFA Bool (Fin 4) := ⟨fun s b => if b then s + 1 else s, 0, {0, 2}⟩

/-- Number of `true`s modulo 2; accept an odd count. -/
def odd : DFA Bool (Fin 2) := ⟨fun s b => if b then s + 1 else s, 0, {1}⟩

/-- State `1` accepts but is never entered. -/
def deadAccept : DFA Bool (Fin 2) := ⟨fun _ _ => 0, 0, {1}⟩

/-- Accept everything. -/
def all : DFA Bool (Fin 1) := ⟨fun _ _ => 0, 0, Set.univ⟩

instance : DecidablePred (· ∈ parity.accept) := inferInstanceAs (DecidablePred (· ∈ ({0} : Set _)))
instance : DecidablePred (· ∈ parity4.accept) :=
  inferInstanceAs (DecidablePred (· ∈ ({0, 2} : Set (Fin 4))))
instance : DecidablePred (· ∈ odd.accept) := inferInstanceAs (DecidablePred (· ∈ ({1} : Set _)))
instance : DecidablePred (· ∈ deadAccept.accept) :=
  inferInstanceAs (DecidablePred (· ∈ ({1} : Set (Fin 2))))
instance : DecidablePred (· ∈ all.accept) :=
  inferInstanceAs (DecidablePred (· ∈ (Set.univ : Set (Fin 1))))

example : parity.equivB parity4 = true := by decide
example : parity.accepts = parity4.accepts := (equivB_iff _ _).1 (by decide)
example : parity.equivB odd = false := by decide
example : parity.isEmptyB = false := by decide
example : deadAccept.isEmptyB = true := by decide
example : deadAccept.accepts = 0 := (isEmptyB_iff _).1 (by decide)
example : (1 : Fin 2) ∉ deadAccept.reachable := by decide
example : all.isUnivB = true := by decide
example : all.accepts = ⊤ := (isUnivB_iff _).1 (by decide)
example : parity.isUnivB = false := by decide

end DFA.RegularTests

namespace Cslib.Automata.EncodedDFA.Tests

/-- Parity of `true`s. -/
def eParity : EncodedDFA Bool := ⟨0, [0], [((0, true), 1), ((1, true), 0)]⟩

/-- Number of `true`s modulo 4, accepting `0` and `2`. -/
def eParity4 : EncodedDFA Bool :=
  ⟨0, [0, 2], [((0, true), 1), ((1, true), 2), ((2, true), 3), ((3, true), 0)]⟩

/-- Odd number of `true`s. -/
def eOdd : EncodedDFA Bool := ⟨0, [1], [((0, true), 1), ((1, true), 0)]⟩

/-- The accepting state `7` is never entered. -/
def eDead : EncodedDFA Bool := ⟨0, [7], [((0, true), 1), ((1, false), 0)]⟩

example : eParity.acceptsB [true, true] = true := by decide
example : eParity.acceptsB [true] = false := by decide
example : eParity.reachable.toFinset = {0, 1} := by decide
example : eParity.isEmptyB = false := by decide
example : eDead.isEmptyB = true := by decide
example : eDead.language = 0 := isEmptyB_iff.1 (by decide)
example : eParity.equivB eParity4 = true := by decide +kernel
example : eParity.language = eParity4.language := equivB_iff.1 (by decide +kernel)
example : eParity.equivB eOdd = false := by decide +kernel

example : Cslib.Decidability.TM2Decidable
    fun p : EncodedDFA Bool × List Bool => p.2 ∈ p.1.language :=
  tm2Decidable_mem_language

example : Cslib.Decidability.TM2Decidable fun D : EncodedDFA Bool => D.language = 0 :=
  tm2Decidable_language_eq_zero

example : Cslib.Decidability.TM2Decidable
    fun p : EncodedDFA Bool × EncodedDFA Bool => p.1.language = p.2.language :=
  tm2Decidable_language_eq

/-- Accepts every word. -/
def eAll : EncodedDFA Bool := ⟨0, [0], []⟩

/-- Only `[true]` reaches the accepting state `1`; state `2` is a dead end (it has no
transitions, so it stays put). -/
def eOne : EncodedDFA Bool :=
  ⟨0, [1], [((0, true), 1), ((0, false), 2), ((1, true), 2), ((1, false), 2)]⟩

instance : FinEnum Bool := FinEnum.ofList [false, true] (by decide)

example : eAll.isUnivB = true := by decide
example : eAll.language = ⊤ := isUnivB_iff.1 (by decide)
example : eParity.isUnivB = false := by decide
example : eParity.language.Infinite := infiniteB_iff.1 (by decide +kernel)
example : ¬ eOne.language.Infinite := fun h => by
  have := infiniteB_iff.2 h
  revert this
  decide +kernel

example : Cslib.Decidability.TM2Decidable fun D : EncodedDFA Bool => D.language = ⊤ :=
  tm2Decidable_language_eq_top

example : Cslib.Decidability.TM2Decidable fun D : EncodedDFA Bool => D.language.Infinite :=
  tm2Decidable_language_infinite

end Cslib.Automata.EncodedDFA.Tests
