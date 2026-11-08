/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Automata.EpsilonNA.Thompson

import Mathlib.Data.List.ReduceOption

/-!
# Tests for Thompson's construction

* The automaton for `(true + false)∗ true` (words ending in `true`) has seven states (two per
  letter occurrence and one for the star), accepts `[false, true]` and rejects `[true, false]`.
* Runs built from the transitions alone, without the correctness theorem: the automaton for
  `true∗` accepts `[true, true]`, and the automaton for `true` has no run on `[false]`.
* The automaton for `0` accepts nothing and the automaton for `1` accepts only the empty word.
-/

@[expose] public section

namespace Cslib.Automata.Thompson.Tests

open Computability

/-- Words over `Bool` that end in `true`. -/
def endsTrue : RegularExpression Bool :=
  (RegularExpression.char true + RegularExpression.char false).star * RegularExpression.char true

example : Fintype.card (State endsTrue) = 7 := rfl

example : [false, true] ∈ (toεNFA endsTrue).accepts := by
  rw [accepts_toεNFA]
  refine ⟨[false], ?_, [true], rfl, rfl⟩
  refine Language.mem_kstar.2 ⟨[[false]], rfl, ?_⟩
  simp only [List.mem_singleton, forall_eq]
  exact Or.inr rfl

example : [true, false] ∉ (toεNFA endsTrue).accepts := by
  rw [accepts_toεNFA]
  rintro ⟨u, -, v, hv, huv⟩
  change v = [true] at hv
  subst hv
  have := congrArg List.getLast? huv
  simp at this

/-- An accepting run of the automaton for `true∗` on `[true, true]`, built from its transitions
without the correctness theorem: `none`, ε to the start of the letter automaton, `true`, ε back
to `none`, twice. -/
example : [true, true] ∈ (toεNFA (RegularExpression.char true).star).accepts := by
  rw [εNFA.mem_accepts_iff_exists_path]
  refine ⟨none, none, [none, some true, none, none, some true, none], rfl, rfl, rfl, ?_⟩
  have hin : (toεNFA (RegularExpression.char true).star).IsPath none (some false) [none] :=
    εNFA.IsPath.cons _ _ _ _ _ ⟨rfl, false, rfl, rfl⟩ (εNFA.IsPath.nil _)
  have hletter :
      (toεNFA (RegularExpression.char true).star).IsPath (some false) (some true) [some true] :=
    εNFA.IsPath.cons _ _ _ _ _ (Or.inl ⟨true, ⟨rfl, rfl, rfl⟩, rfl⟩) (εNFA.IsPath.nil _)
  have hout : (toεNFA (RegularExpression.char true).star).IsPath (some true) none [none] :=
    εNFA.IsPath.cons _ _ _ _ _ (Or.inr ⟨rfl, rfl, rfl⟩) (εNFA.IsPath.nil _)
  have hloop : (toεNFA (RegularExpression.char true).star).IsPath none none
      [none, some true, none] :=
    (εNFA.isPath_append _).2 ⟨_, hin, (εNFA.isPath_append _).2 ⟨_, hletter, hout⟩⟩
  exact (εNFA.isPath_append _).2 ⟨none, hloop, hloop⟩

/-- The letter automaton has no move on another letter, so `[false]` has no accepting run. -/
example : [false] ∉ (toεNFA (RegularExpression.char true)).accepts := by
  rw [εNFA.mem_accepts_iff_exists_path]
  rintro ⟨s, t, x, hs, ht, hx, hpath⟩
  change s = false at hs
  change t = true at ht
  subst hs ht
  cases hpath with
  | cons v _ _ c x hv _ =>
      obtain ⟨-, rfl, rfl⟩ := hv
      simp at hx

example : (toεNFA (0 : RegularExpression Bool)).accepts = 0 := accepts_toεNFA _

example : (toεNFA (1 : RegularExpression Bool)).accepts = 1 := accepts_toεNFA _

end Cslib.Automata.Thompson.Tests
