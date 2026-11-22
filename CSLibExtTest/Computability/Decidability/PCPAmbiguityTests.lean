/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Decidability.PCPAmbiguity

@[expose] public section

/-!
# Tests for the reduction of PCP to ambiguity of context-free grammars
-/

set_option autoImplicit false

open Cslib.Language Cslib.Decidability.Post Cslib.Decidability.Grammar

namespace CSLibExtTest.Computability.Decidability.PCPAmbiguity

/-- A solvable instance gives an ambiguous grammar. -/
example : IsAmbiguous (ambGrammar [([true], [true])]).toCFG :=
  (isAmbiguous_iff_pcp _).mpr ⟨[([true], [true])], by simp, by simp, rfl⟩

/-- The two leftmost derivations of the word `1 0` of the instance `[(1, 1)]`. -/
example : LeftDerivation (ambGrammar [([true], [true])]).toCFG [Symbol.nonterminal 0]
    [Sum.inl true, Sum.inr 0] (startRule 1 :: canon Prod.fst 1 [([true], [true])] [0]) :=
  leftDerivation_start (is := [0]) (Or.inl ⟨rfl, rfl⟩) (by simp) (by simp)

example : LeftDerivation (ambGrammar [([true], [true])]).toCFG [Symbol.nonterminal 0]
    [Sum.inl true, Sum.inr 0] (startRule 2 :: canon Prod.snd 2 [([true], [true])] [0]) :=
  leftDerivation_start (is := [0]) (Or.inr ⟨rfl, rfl⟩) (by simp) (by simp)

/-- An unsolvable instance gives an unambiguous grammar. -/
example : ¬IsAmbiguous (ambGrammar [([true], [false])]).toCFG := by
  rw [isAmbiguous_iff_pcp]
  rintro ⟨s, hne, hmem, htop⟩
  obtain ⟨d, s, rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain rfl : d = ([true], [false]) := by simpa using hmem d List.mem_cons_self
  simp [top, bottom] at htop

/-- The reduction, over `Bool`. -/
example : ManyOneReducible (PCP (α := Bool)) fun g : EncodedCFG (Bool ⊕ ℕ) ↦ IsAmbiguous g.toCFG :=
  manyOneReducible_pcp_isAmbiguous

end CSLibExtTest.Computability.Decidability.PCPAmbiguity
