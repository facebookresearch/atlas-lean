/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Decidability.ContextFreeRegular

/-!
# Tests for emptiness of a context-free language intersected with a regular language

Over `Bool`, with `anbn` the grammar `S → true S false | ε`:

* `noFalse` accepts the words without `false`: the intersection with `anbn` is `{[]}`, so it is
  not empty.
* `endsTrue` accepts the words ending in `true`: no word of `anbn` does, so the intersection is
  empty.
* `sorted` accepts the words with no `true` after a `false`: `anbn` is included in it, but not in
  `noFalse`.
* The complement of `noFalse` rejects `[]` and accepts `[false]`.
* Both multi-stack decidability statements instantiated.
-/

@[expose] public section

namespace Cslib.Language.EncodedCFG.InterRegularTests

open Cslib.Automata

/-- `S → true S false | ε`. -/
def anbn : EncodedCFG Bool := ⟨0, [(0, [.inr true, .inl 0, .inr false]), (0, [])]⟩

/-- The words without `false`: `false` leads to the dead state `1`. -/
def noFalse : EncodedDFA Bool := ⟨0, [0], [((0, false), 1)]⟩

/-- The words ending in `true`. -/
def endsTrue : EncodedDFA Bool := ⟨0, [1], [((0, true), 1), ((1, false), 0)]⟩

/-- The words with no `true` after a `false`. -/
def sorted : EncodedDFA Bool := ⟨0, [0, 1], [((0, false), 1), ((1, true), 2)]⟩

example : interEmptyB anbn noFalse = false := by decide +kernel
example : anbn.language ⊓ noFalse.language ≠ 0 := fun h => by
  have := interEmptyB_iff.2 h
  revert this
  decide +kernel
example : anbn.language ⊓ endsTrue.language = 0 := interEmptyB_iff.1 (by decide +kernel)
example : anbn.language ≤ sorted.language := subsetB_iff.1 (by decide +kernel)
example : subsetB anbn noFalse = false := by decide +kernel

example : [] ∉ noFalse.compl.language := by
  rw [EncodedDFA.mem_language_compl]
  decide
example : [false] ∈ noFalse.compl.language := by
  rw [EncodedDFA.mem_language_compl]
  decide

example : Cslib.Decidability.TM2Decidable
    fun p : EncodedCFG Bool × EncodedDFA Bool => p.1.language ⊓ p.2.language = 0 :=
  tm2Decidable_inter_eq_zero

example : Cslib.Decidability.TM2Decidable
    fun p : EncodedCFG Bool × EncodedDFA Bool => p.1.language ≤ p.2.language :=
  tm2Decidable_language_le

end Cslib.Language.EncodedCFG.InterRegularTests
