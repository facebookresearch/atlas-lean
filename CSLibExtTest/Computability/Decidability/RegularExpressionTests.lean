/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Decidability.RegularExpression

/-!
# Tests for encoded regular expressions

* `endsTrue` encodes `(true + false)* true` as six nodes; its root expression is that Mathlib
  regular expression, and `flatten` of the Mathlib expression gives back the same nodes.
* The grammar of `endsTrue` accepts `[true]` and `[false, true]` and rejects `[]` and
  `[true, false]`, all checked by running the A_CFG decider in the kernel.
* `badChild` has a `plus` node whose second argument points forward; it reads as `0`, so the
  expression is `true + 0`. The empty encoding denotes `0`.
* Emptiness: `endsTrue` is not empty and `0 true` is, by the E_CFG decider.
* Infiniteness, by the structural flag pass, run in the kernel: `endsTrue` and `(true + false)*`
  are infinite; the single letter `true`, `ε*` and `true* 0` are finite.
* Inclusion: `endsTrue` is contained in the language of the DFA `lastTrue` (words ending in
  `true`) and not in that of `onlyFalse`, by the CFG ⊆ DFA decider.
* Membership through `memB_iff`, `toRegex_flatten`, and the multi-stack decidability statements
  (Sipser 4.3 and E_REX) instantiated.
-/

@[expose] public section

namespace Cslib.Language.EncodedRegex.Tests

/-- `(true + false)* true`: nodes `0 = true`, `1 = false`, `2 = 0 + 1`, `3 = 2*`, `4 = true`,
`5 = 3 4`. -/
def endsTrue : EncodedRegex Bool :=
  ⟨[.char true, .char false, .plus 0 1, .star 2, .char true, .comp 3 4]⟩

/-- The same expression in Mathlib's syntax. -/
def endsTrueRegex : RegularExpression Bool :=
  .comp (.star (.plus (.char true) (.char false))) (.char true)

example : (flatten endsTrueRegex).nodes = endsTrue.nodes := rfl
example : endsTrue.toRegex = endsTrueRegex := by
  rw [show endsTrue = flatten endsTrueRegex from rfl, toRegex_flatten]

example : endsTrue.memB [true] = true := by decide +kernel
example : endsTrue.memB [false, true] = true := by decide +kernel
example : endsTrue.memB [] = false := by decide +kernel
example : endsTrue.memB [true, false] = false := by decide +kernel

example : [false, true] ∈ endsTrue.toRegex.matches' := memB_iff.1 (by decide +kernel)

/-- A `plus` node whose second argument (`5`) is not an earlier node. -/
def badChild : EncodedRegex Bool :=
  ⟨[.char true, .plus 0 5]⟩

example : badChild.toRegex = .char true + 0 := by
  rw [toRegex, show badChild.nodes.length - 1 = 1 from rfl,
    regexAt_of_plus (show badChild.node 1 = .plus 0 5 from rfl),
    ite_eq_left (show 0 < 1 by decide), ite_eq_right (show ¬5 < 1 by decide),
    regexAt_of_char (show badChild.node 0 = .char true from rfl)]

example (r : RegularExpression Bool) : (flatten r).toRegex = r := toRegex_flatten r

/-- The empty encoding denotes `0`. -/
example : (⟨[]⟩ : EncodedRegex Bool).toRegex = 0 :=
  regexAt_of_zero (node_of_le (Nat.zero_le _))

example : endsTrue.isEmptyB = false := by decide +kernel
/-- `0 true`: empty. -/
example : (⟨[.zero, .char true, .comp 0 1]⟩ : EncodedRegex Bool).isEmptyB = true := by
  decide +kernel

example : Cslib.Decidability.TM2Decidable
    fun e : EncodedRegex Bool => e.toRegex.matches' = 0 :=
  tm2Decidable_matches_eq_zero

/-- The single letter `true` matches a finite language. -/
example : (⟨[.char true]⟩ : EncodedRegex Bool).infiniteB = false := by decide +kernel

example : endsTrue.infiniteB = true := by decide +kernel

/-- `(true + false)*` is infinite. -/
example :
    (⟨[.char true, .char false, .plus 0 1, .star 2]⟩ : EncodedRegex Bool).infiniteB = true := by
  decide +kernel

/-- `ε*` matches only the empty word. -/
example : (⟨[.epsilon, .star 0]⟩ : EncodedRegex Bool).infiniteB = false := by decide +kernel

/-- `true* 0` is empty, so finite, although `true*` is infinite. -/
example : (⟨[.char true, .star 0, .zero, .comp 1 2]⟩ : EncodedRegex Bool).infiniteB = false := by
  decide +kernel

example : Cslib.Decidability.TM2Decidable
    fun e : EncodedRegex Bool => e.toRegex.matches'.Infinite :=
  tm2Decidable_matches_infinite

/-- The last letter read (`0` initially and after `false`, `1` after `true`); accepts the words
ending in `true`. -/
def lastTrue : Cslib.Automata.EncodedDFA Bool :=
  ⟨0, [1], [((0, true), 1), ((1, false), 0)]⟩

/-- The words over `{false}`: state `0`, and a dead state `1` after `true`. -/
def onlyFalse : Cslib.Automata.EncodedDFA Bool :=
  ⟨0, [0], [((0, true), 1)]⟩

example : endsTrue.subsetB lastTrue = true := by decide +kernel
example : endsTrue.subsetB onlyFalse = false := by decide +kernel

example : Cslib.Decidability.TM2Decidable
    fun p : EncodedRegex Bool × Cslib.Automata.EncodedDFA Bool =>
      p.1.toRegex.matches' ≤ p.2.language :=
  tm2Decidable_matches_le

example : Cslib.Decidability.TM2Decidable
    fun p : EncodedRegex Bool × List Bool => p.2 ∈ p.1.toRegex.matches' :=
  tm2Decidable_mem_matches

end Cslib.Language.EncodedRegex.Tests
