/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Decidability.CFGUndecidable

@[expose] public section

/-!
# Tests for the reduction of PCP to intersection of context-free languages
-/

set_option autoImplicit false

open Cslib.Language Cslib.Decidability.Post Cslib.Decidability.Grammar

namespace CSLibExtTest.Computability.Decidability.CFGUndecidable

/-- The word `t₀ t₀ 0 0` of the top grammar of `[(1, 1)]`. -/
example : [Sum.inl true, Sum.inl true, Sum.inr 0, Sum.inr 0] ∈
    (sideGrammar Prod.fst [([true], [true])]).language :=
  mem_language_sideGrammar.mpr ⟨[0, 0], by simp, by simp, rfl⟩

/-- A solvable instance: the two grammars share a word. -/
example : ∃ w, w ∈ (sideGrammar Prod.fst [([true], [true])]).language ∧
    w ∈ (sideGrammar Prod.snd [([true], [true])]).language :=
  (pcp_iff_exists_mem_inter _).mp ⟨[([true], [true])], by simp, by simp, rfl⟩

/-- An unsolvable instance: tops start with `1` and bottoms with `0`. -/
theorem not_pcp_10 : ¬PCP [([true], [false])] := by
  rintro ⟨s, hne, hmem, htop⟩
  obtain ⟨d, s, rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain rfl : d = ([true], [false]) := by simpa using hmem d List.mem_cons_self
  simp [top, bottom] at htop

example : ¬∃ w, w ∈ (sideGrammar Prod.fst [([true], [false])]).language ∧
    w ∈ (sideGrammar Prod.snd [([true], [false])]).language :=
  fun h ↦ not_pcp_10 ((pcp_iff_exists_mem_inter _).mpr h)

/-- The reduction, over `Bool`. -/
example : ManyOneReducible (PCP (α := Bool)) fun g : EncodedCFG (Bool ⊕ ℕ) × EncodedCFG (Bool ⊕ ℕ) ↦
    ∃ w, w ∈ g.1.language ∧ w ∈ g.2.language :=
  manyOneReducible_pcp_inter

end CSLibExtTest.Computability.Decidability.CFGUndecidable
