/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# REYNOLDS COVERING FOR CONTEXT-FREE GRAMMARS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AL11] REYNOLDS COVERING FOR
CONTEXT-FREE GRAMMARS;
H. B. Hunt III and D. J. Rosenkrantz, "Complexity of grammatical similarity relations:
preliminary report", Proc. Conference on Theoretical Computer Science, University of
Waterloo (1977), 139-148.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Languages.ContextFree.Encoded
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ReynoldsCovering

/-!
# REYNOLDS COVERING FOR CONTEXT-FREE GRAMMARS is NP-complete

Given context-free grammars `G₁ = (N₁, Σ, Π₁, S₁)` and `G₂ = (N₂, Σ, Π₂, S₂)` over the same
terminal alphabet, does `G₂` Reynolds cover `G₁`: is there a function `f` from `N₁ ∪ Σ` to
`N₂ ∪ Σ` with `f x = x` for every terminal `x`, `f A ∈ N₂` for every `A ∈ N₁`,
`f S₁ = S₂`, and such that for every production `A → x₁ ⋯ xᵣ` of `Π₁` the image
`f A → f x₁ ⋯ f xᵣ` is a production of `Π₂`?

The terminal alphabet is `Σ = {0, ..., k - 1}` and the nonterminals of a grammar with `n`
nonterminals are `0, ..., n - 1`. A production is a pair of a left-hand side and a list of
right-hand side symbols, in which `(false, B)` is nonterminal `B` and `(true, a)` is terminal
`a`; the set of productions is a list (a repeated production does not change the grammar).
Each grammar is read as a `Cslib.Language.EncodedCFG`, whose `toCFG` is a Mathlib
`ContextFreeGrammar` with nonterminals `ℕ`. Since `f` is the identity on terminals, it is
determined by its values on nonterminals, a map `f : ℕ → ℕ`, and the image of a production
is `Cslib.Language.mapRule f`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A context-free grammar as data: the number `n` of nonterminals (they are
`0, ..., n - 1`), the initial nonterminal, and the productions. A production `(A, w)` has
left-hand side `A` and right-hand side `w`, in which `(false, B)` is nonterminal `B` and
`(true, a)` is terminal `a`. -/
abbrev GrammarData := ℕ × ℕ × List (ℕ × List (Bool × ℕ))

/-- An instance: the number `k` of terminals (the terminal alphabet is `{0, ..., k - 1}`)
and the grammars `G₁` and `G₂`. -/
abbrev ReynoldsCoveringInstance := ℕ × GrammarData × GrammarData

/-- A right-hand side symbol as a symbol of `Cslib.Language.EncodedCFG`: `Sum.inl B` is
nonterminal `B` and `Sum.inr a` is terminal `a`. -/
def toSum : Bool × ℕ → ℕ ⊕ ℕ
  | (false, B) => .inl B
  | (true, a) => .inr a

/-- The grammar a `GrammarData` denotes, as a `Cslib.Language.EncodedCFG` over the terminals
`ℕ`. -/
def toEncodedCFG (g : GrammarData) : Cslib.Language.EncodedCFG ℕ :=
  ⟨g.2.1, g.2.2.map fun p => (p.1, p.2.map toSum)⟩

/-- A grammar is well-formed over `k` terminals when its initial symbol is one of its `n`
nonterminals and every production has its left-hand side among the nonterminals, and every
right-hand side symbol is a nonterminal below `n` or a terminal below `k`. -/
def GrammarWellFormed (k : ℕ) (g : GrammarData) : Prop :=
  g.2.1 < g.1 ∧ ∀ p ∈ g.2.2, p.1 < g.1 ∧ ∀ x ∈ p.2, if x.1 then x.2 < k else x.2 < g.1

/-- Well-formedness of an instance: both grammars are well-formed over the shared terminal
alphabet `{0, ..., k - 1}`. -/
def WellFormed : ReynoldsCoveringInstance → Prop
  | (k, g₁, g₂) => GrammarWellFormed k g₁ ∧ GrammarWellFormed k g₂

/-- `G₂` Reynolds covers `G₁`: some map `f` on nonterminals (extended by the identity on
terminals) sends every nonterminal of `G₁` to a nonterminal of `G₂` and the initial symbol of
`G₁` to that of `G₂`, and sends every production of `G₁` to a production of `G₂`. -/
def ReynoldsCoveringFeasible : ReynoldsCoveringInstance → Prop
  | (_, g₁, g₂) =>
    ∃ f : ℕ → ℕ, (∀ A < g₁.1, f A < g₂.1) ∧
      f (toEncodedCFG g₁).toCFG.initial = (toEncodedCFG g₂).toCFG.initial ∧
      ∀ r ∈ (toEncodedCFG g₁).toCFG.rules,
        Cslib.Language.mapRule f r ∈ (toEncodedCFG g₂).toCFG.rules

open Classical in
/-- REYNOLDS COVERING FOR CONTEXT-FREE GRAMMARS as a decision problem over bitstrings. -/
noncomputable def reynoldsCoveringDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ReynoldsCoveringInstance) x with
  | some i => decide (WellFormed i ∧ ReynoldsCoveringFeasible i)
  | none => false

/-- **REYNOLDS COVERING FOR CONTEXT-FREE GRAMMARS is NP-complete.** Source: Garey and
Johnson (1979), [AL11]; Hunt and Rosenkrantz (1977). -/
public theorem_wanted reynoldsCovering_npComplete :
    reynoldsCoveringDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L reynoldsCoveringDec

end MetaMathlibExt.Complexity.NPComplete.ReynoldsCovering
