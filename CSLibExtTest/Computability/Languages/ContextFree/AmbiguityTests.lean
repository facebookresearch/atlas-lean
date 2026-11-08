/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.Ambiguity

@[expose] public section

/-!
# Tests for leftmost derivations and ambiguity
-/

set_option autoImplicit false

open Cslib.Language

namespace CSLibExtTest.Computability.Languages.ContextFree.Ambiguity

/-- `S → A | B`, `A → a`, `B → a`, with `S, A, B = 0, 1, 2`. -/
abbrev g : ContextFreeGrammar Bool where
  NT := ℕ
  initial := 0
  rules := {⟨0, [.nonterminal 1]⟩, ⟨0, [.nonterminal 2]⟩, ⟨1, [.terminal true]⟩,
    ⟨2, [.terminal true]⟩}

theorem leftDerivation_via (A : ℕ) (hA : A = 1 ∨ A = 2) :
    LeftDerivation g [.nonterminal 0] [true] [⟨0, [.nonterminal A]⟩, ⟨A, [.terminal true]⟩] := by
  have h₁ : (⟨0, [.nonterminal A]⟩ : ContextFreeRule Bool ℕ) ∈ g.rules := by
    rcases hA with rfl | rfl <;> decide
  have h₂ : (⟨A, [.terminal true]⟩ : ContextFreeRule Bool ℕ) ∈ g.rules := by
    rcases hA with rfl | rfl <;> decide
  exact LeftDerivation.step (p := []) (v := []) h₁
    (LeftDerivation.step (p := []) (v := []) h₂ (LeftDerivation.done [true]))

/-- The word `a` has two leftmost derivations, so `g` is ambiguous. -/
example : IsAmbiguous g := by
  refine ⟨[true], _, _, ?_, leftDerivation_via 1 (Or.inl rfl), leftDerivation_via 2 (Or.inr rfl)⟩
  simp

/-- Leftmost derivations are derivations. -/
example : [true] ∈ g.language := (leftDerivation_via 1 (Or.inl rfl)).mem_language

/-- From a word of terminals the only leftmost derivation is empty. -/
example (w : List Bool) (rs : List (ContextFreeRule Bool ℕ))
    (h : LeftDerivation g ([true, false].map Symbol.terminal) w rs) : rs = [] ∧ w = [true, false] :=
  h.eq_of_terminal

end CSLibExtTest.Computability.Languages.ContextFree.Ambiguity
