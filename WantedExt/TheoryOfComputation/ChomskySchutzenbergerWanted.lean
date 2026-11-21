/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Computability.ContextFreeGrammar
public import Mathlib.Computability.DFA

/-!
# Chomsky-Schützenberger theorem: every context-free language is a
homomorphic image of a Dyck language intersected with a regular language

The statement is registered here as a `theorem_wanted`, with the Dyck
language defined below. The proof encodes derivation trees of a
grammar as correctly bracketed words (one bracket pair per
production), intersects with a regular language checking that
adjacent brackets correspond to a valid derivation, and maps brackets
to the terminals they produce. Building the encoding grammar and the
regular side condition in Lean is a large construction, so the theorem
is left as a `theorem_wanted`.
-/

@[expose] public section

namespace Cslib.ChomskySchutzenbergerWanted

/-- A Dyck word over `k` bracket pairs: the empty word is Dyck,
concatenations of Dyck words are Dyck, and wrapping a Dyck word in a
matched pair of brackets of the same kind is Dyck. The letter
`(i, true)` is the opening bracket of kind `i` and `(i, false)` its
closing bracket.
Source: Chomsky and Schützenberger, "The algebraic theory of
context-free languages", in Computer Programming and Formal Systems,
North-Holland, 1963, 118-161. -/
public inductive IsDyckWord {k : ℕ} : List (Fin k × Bool) → Prop
  | nil : IsDyckWord []
  | append {w₁ w₂ : List (Fin k × Bool)} (h₁ : IsDyckWord w₁)
      (h₂ : IsDyckWord w₂) :
      IsDyckWord (w₁ ++ w₂)
  | wrap {i : Fin k} {w : List (Fin k × Bool)} (h : IsDyckWord w) :
      IsDyckWord ((i, true) :: w ++ [(i, false)])

/-- The Dyck language over `k` bracket pairs: all Dyck words.
Source: Chomsky and Schützenberger, "The algebraic theory of
context-free languages", in Computer Programming and Formal Systems,
North-Holland, 1963, 118-161. -/
public def dyckLanguage (k : ℕ) : Language (Fin k × Bool) :=
  {w | IsDyckWord w}

/-- Every context-free language is the homomorphic image of the
intersection of a Dyck language with a regular language: for some
number `k` of bracket pairs, some regular language `R` over the
bracket alphabet, and some word homomorphism `φ`, the language is
`φ (Dyck_k ∩ R)`.
Source: Chomsky and Schützenberger, "The algebraic theory of
context-free languages", in Computer Programming and Formal Systems,
North-Holland, 1963, 118-161. -/
public theorem_wanted chomsky_schutzenberger {T : Type*} {L : Language T}
    (hL : L.IsContextFree) :
    ∃ (k : ℕ) (R : Language (Fin k × Bool)) (φ : (Fin k × Bool) → List T),
      R.IsRegular ∧
        L = {y | ∃ x ∈ dyckLanguage k ⊓ R, (x.map φ).flatten = y}

end Cslib.ChomskySchutzenbergerWanted
