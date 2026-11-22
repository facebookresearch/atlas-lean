/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Automata.NA.EncodedNFA

/-!
# Tests for encoded NFAs

* `secondLast` accepts the words whose second-to-last letter is `true`: state `0` loops and may
  guess the position on `true`. It accepts `[true, false]` and `[true, true, false]` and rejects
  `[false, true]`, `[true]` and `[true, false, false]`; the states reached on `[true]` are `0`
  and `1`.
* `withEps` uses ε-moves before and after letters: `0 -ε-> 1 -true-> 2` and
  `0 -false-> 3 -ε-> 2`, accepting state `2`. It accepts `[true]` and `[false]` and rejects `[]`
  and `[true, true]`; the ε-closure of the start state is `{0, 1}`.
* Emptiness: `secondLast` and `withEps` are not empty; an NFA whose accepting state is reached
  only through an ε-move from an unreachable state is.
* `exists_language_eq`, `exists_language_eq_εNFA` and both multi-stack decidability statements
  (Sipser 4.2 and E_NFA) instantiated.
-/

@[expose] public section

namespace Cslib.Automata.EncodedNFA.Tests

/-- The words whose second-to-last letter is `true`. -/
def secondLast : EncodedNFA Bool :=
  ⟨[0], [2], [((0, true), 0), ((0, false), 0), ((0, true), 1), ((1, true), 2), ((1, false), 2)],
    []⟩

example : secondLast.run [true] = [0, 1] := by decide
example : ∀ w ∈ [[true, false], [true, true, false]], secondLast.acceptsB w = true := by decide
example : ∀ w ∈ [[false, true], [true], [true, false, false]], secondLast.acceptsB w = false := by
  decide

example : [true, false] ∈ secondLast.language := acceptsB_iff.1 (by decide)
example : [false, true] ∉ secondLast.language := by decide

/-- ε-moves before and after letters: `0 -ε-> 1 -true-> 2`, `0 -false-> 3 -ε-> 2`. -/
def withEps : EncodedNFA Bool :=
  ⟨[0], [2], [((1, true), 2), ((0, false), 3)], [(0, 1), (3, 2)]⟩

example : withEps.closure withEps.start = [0, 1] := by decide
example : ∀ w ∈ [[true], [false]], withEps.acceptsB w = true := by decide
example : ∀ w ∈ [[], [true, true]], withEps.acceptsB w = false := by decide

example : secondLast.isEmptyB = false := by decide
example : withEps.isEmptyB = false := by decide
/-- The accepting state `2` is reached only by an ε-move from `5`, which nothing reaches. -/
example : (⟨[0], [2], [((0, true), 1)], [(5, 2)]⟩ : EncodedNFA Bool).isEmptyB = true := by
  decide

example (M : NFA Bool (Fin 3)) : ∃ N : EncodedNFA Bool, N.language = M.accepts :=
  exists_language_eq M

example (M : εNFA Bool (Fin 3)) : ∃ N : EncodedNFA Bool, N.language = M.accepts :=
  exists_language_eq_εNFA M

example : Cslib.Decidability.TM2Decidable
    fun p : EncodedNFA Bool × List Bool => p.2 ∈ p.1.language :=
  tm2Decidable_mem_language

example : Cslib.Decidability.TM2Decidable fun N : EncodedNFA Bool => N.language = 0 :=
  tm2Decidable_language_eq_zero

end Cslib.Automata.EncodedNFA.Tests
