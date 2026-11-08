/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Automata.DA.EncodedDFA

/-!
# Tests for encoded DFAs

* `parity`, over `Bool`, has states `0, 1` and transitions on `true` only: reading `false` stays
  put, so it accepts the words with an even number of `true`s.
* With two transitions listed for the same state and letter, the first applies.
* Every finite DFA has an encoding with the same language.
* Running an encoded DFA is primitive recursive.
-/

@[expose] public section

namespace Cslib.Automata.EncodedDFA.Tests

/-- Parity of `true`s: `0 → 1 → 0` on `true`, no transitions on `false`. -/
def parity : EncodedDFA Bool := ⟨0, [0], [((0, true), 1), ((1, true), 0)]⟩

example : parity.step 0 true = 1 := by decide
example : parity.step 1 false = 1 := by decide
example : parity.toDFA.eval [true, false, true] = 0 := by decide
example : [true, false, true] ∈ parity.language := by decide
example : [true, false] ∉ parity.language := by decide

/-- Two transitions for `(0, true)`: the first, to `2`, applies. -/
def shadowed : EncodedDFA Bool := ⟨0, [2], [((0, true), 2), ((0, true), 1)]⟩

example : shadowed.step 0 true = 2 := by decide

example {σ : Type} [Finite σ] (M : DFA Bool σ) : ∃ D : EncodedDFA Bool, D.language = M.accepts :=
  exists_language_eq M

example : Primrec₂ fun (D : EncodedDFA Bool) (w : List Bool) => D.toDFA.eval w := primrec₂_eval

end Cslib.Automata.EncodedDFA.Tests
