/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Decidability.PCPUniversality

@[expose] public section

/-!
# Tests for the reduction of the complement of PCP to universality of context-free grammars
-/

set_option autoImplicit false

open Cslib.Language Cslib.Decidability.Post Cslib.Decidability.Grammar

namespace CSLibExtTest.Computability.Decidability.PCPUniversality

/-- The word `1 |` of the top list language of `[(1, 1)]`. -/
example : [Sum.inl true, Sum.inr true] ∈ listLang Prod.fst [([true], [true])] :=
  ⟨[0], by simp, by simp, rfl⟩

/-- Index codes are uniquely decodable. -/
example : bitCodes [2, 0] = [true, false, false, true] := rfl

/-- A solvable instance: the universality grammar misses the solution word. -/
example : ¬∀ w, w ∈ (univGrammar [([true], [true])]).language :=
  fun h ↦ (forall_mem_language_univGrammar_iff _).mp h ⟨[([true], [true])], by simp, by simp, rfl⟩

/-- The word with no index bits is malformed, so it is generated. -/
example : [Sum.inl true, Sum.inl false] ∈ (univGrammar [([true], [true])]).language := by
  rw [language_univGrammar]
  exact Or.inl (Or.inl ⟨[true, false], rfl⟩)

/-- An unsolvable instance: tops start with `1` and bottoms with `0`, so the universality grammar
generates every word. -/
example : ∀ w, w ∈ (univGrammar [([true], [false])]).language := by
  rw [forall_mem_language_univGrammar_iff]
  rintro ⟨s, hne, hmem, htop⟩
  obtain ⟨d, s, rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain rfl : d = ([true], [false]) := by simpa using hmem d List.mem_cons_self
  simp [top, bottom] at htop

/-- The reduction, over `Bool`. -/
example : ManyOneReducible (fun P : List (Domino Bool) ↦ ¬PCP P)
    fun g : EncodedCFG (Bool ⊕ Bool) ↦ ∀ w, w ∈ g.language :=
  manyOneReducible_not_pcp_univ

end CSLibExtTest.Computability.Decidability.PCPUniversality
