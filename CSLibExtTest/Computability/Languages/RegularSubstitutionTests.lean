/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.RegularSubstitution

/-!
# Tests for substitution into regular languages

* `endsTrueDFA` accepts the words ending in `true`. Substituting the words with an even number of
  `true`s for `true`, and all words for `false`, gives a regular language containing
  `[true, true]` (from `[true]`) and `[]` (from `[false, true]` with the empty word for both
  letters).
* The ε-NFA of the construction accepts exactly the substitution image
  (`RegularSubstitution.accepts_εnfa`), and the generic statement is instantiated.
-/

@[expose] public section

namespace Cslib.Language.RegularSubstitutionTests

/-- The last letter read; accepts the words ending in `true`. -/
def endsTrueDFA : DFA Bool Bool :=
  ⟨fun _ b => b, false, {true}⟩

/-- The parity of the number of `true`s; accepts even counts. -/
def evenTrue : DFA Bool Bool :=
  ⟨fun p b => xor p b, false, {false}⟩

/-- All words. -/
def allWords : DFA Bool Unit :=
  ⟨fun _ _ => (), (), Set.univ⟩

/-- `true ↦` the words with an even number of `true`s, `false ↦` all words. -/
def s : Bool → Language Bool
  | true => evenTrue.accepts
  | false => allWords.accepts

theorem s_isRegular : ∀ b, (s b).IsRegular
  | true => ⟨Bool, inferInstance, evenTrue, rfl⟩
  | false => ⟨Unit, inferInstance, allWords, rfl⟩

example : (substitution endsTrueDFA.accepts s).IsRegular :=
  IsRegular.substitution ⟨Bool, inferInstance, endsTrueDFA, rfl⟩ s_isRegular

example : [true, true] ∈ substitution endsTrueDFA.accepts s := by
  refine ⟨[true], rfl, ?_⟩
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  exact rfl

example : [] ∈ substitution endsTrueDFA.accepts s := by
  refine ⟨[false, true], rfl, ?_⟩
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  exact Language.mem_mul.2 ⟨[], trivial, [], rfl, rfl⟩

example : (RegularSubstitution.εnfa endsTrueDFA (τ := fun _ => Bool) fun _ => evenTrue).accepts =
    {y | ∃ w ∈ endsTrueDFA.accepts, y ∈ (w.map fun _ => evenTrue.accepts).prod} :=
  RegularSubstitution.accepts_εnfa _ _

example {T T' : Type} [Finite T] {L : Language T} (hL : L.IsRegular) {t : T → Language T'}
    (ht : ∀ a, (t a).IsRegular) : (substitution L t).IsRegular :=
  IsRegular.substitution hL ht

end Cslib.Language.RegularSubstitutionTests
