/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STRUCTURAL INEQUIVALENCE FOR LINEAR GRAMMARS over a one-letter alphabet is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AL13] STRUCTURAL INEQUIVALENCE
FOR LINEAR GRAMMARS, comment ("NP-complete if `|Σ| = 1`");
H. B. Hunt III, D. J. Rosenkrantz and T. G. Szymanski, "On the equivalence, containment,
and covering problems for the regular and context-free languages", Journal of Computer and
System Sciences 12 (1976), 222-268, doi:10.1016/S0022-0000(76)80038-4.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.QuasiRealTimeLanguageMembershipWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.StructuralInequivalenceUnaryLinearGrammars

open MetaMathlibExt.Complexity.NPComplete.QuasiRealTimeLanguageMembership
  (GrammarData toEncodedCFG GrammarWellFormed)

/-!
# STRUCTURAL INEQUIVALENCE FOR LINEAR GRAMMARS over a one-letter alphabet is NP-complete

Given two linear context-free grammars `G₁ = (N₁, Σ, Π₁, S₁)` and `G₂ = (N₂, Σ, Π₂, S₂)`
over a one-letter terminal alphabet `Σ` (`|Σ| = 1`), are `G₁` and `G₂` structurally
inequivalent, that is, do the parenthesized grammars obtained from `G₁` and `G₂` by replacing
each production `A → w` by `A → (w)`, where `(` and `)` are new terminal symbols, generate
different languages? A grammar is linear when no production has more than one nonterminal
symbol on its right-hand side.

The terminal alphabet is `Σ = {0, ..., k - 1}` with `k = 1`, and the two new terminals `(`
and `)` are `k` and `k + 1`. The nonterminals of a grammar with `n` nonterminals are
`0, ..., n - 1`. A production is a pair of a left-hand side and a list of right-hand side
symbols, in which `(false, B)` is nonterminal `B` and `(true, a)` is terminal `a`; the set of
productions is a list (a repeated production does not change the grammar), and right-hand
sides may be empty. Each grammar is read as a `Cslib.Language.EncodedCFG`, whose language is
that of a Mathlib `ContextFreeGrammar` with nonterminals `ℕ`. This grammar encoding
(`GrammarData`, `toEncodedCFG`, `GrammarWellFormed`) is the one of
`WantedExt.Complexity.NPComplete.QuasiRealTimeLanguageMembershipWanted`, reused here.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `k` of terminals (the terminal alphabet is `{0, ..., k - 1}`)
and the grammars `G₁` and `G₂`. -/
abbrev StructuralInequivalenceUnaryLinearGrammarsInstance := ℕ × GrammarData × GrammarData

/-- A grammar is linear when no production has more than one nonterminal symbol on its
right-hand side. -/
def IsLinear (g : GrammarData) : Prop :=
  ∀ p ∈ g.2.2, (p.2.filter fun x => !x.1).length ≤ 1

/-- The parenthesized grammar over the terminals `{0, ..., k + 1}`: every production
`A → w` is replaced by `A → (w)`, where `(` is the new terminal `k` and `)` is the new
terminal `k + 1`. -/
def parenthesize (k : ℕ) (g : GrammarData) : GrammarData :=
  (g.1, g.2.1, g.2.2.map fun p => (p.1, (true, k) :: p.2 ++ [(true, k + 1)]))

/-- Well-formedness of an instance: the terminal alphabet has exactly one letter (`k = 1`),
and both grammars are well-formed over it and linear. -/
def WellFormed : StructuralInequivalenceUnaryLinearGrammarsInstance → Prop
  | (k, g₁, g₂) =>
    k = 1 ∧ GrammarWellFormed k g₁ ∧ GrammarWellFormed k g₂ ∧ IsLinear g₁ ∧ IsLinear g₂

/-- `G₁` and `G₂` are structurally inequivalent: their parenthesized grammars generate
different languages. -/
def StructuralInequivalenceUnaryLinearGrammarsFeasible :
    StructuralInequivalenceUnaryLinearGrammarsInstance → Prop
  | (k, g₁, g₂) =>
    (toEncodedCFG (parenthesize k g₁)).language ≠ (toEncodedCFG (parenthesize k g₂)).language

open Classical in
/-- STRUCTURAL INEQUIVALENCE FOR LINEAR GRAMMARS over a one-letter alphabet as a decision
problem over bitstrings. -/
noncomputable def structuralInequivalenceUnaryLinearGrammarsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := StructuralInequivalenceUnaryLinearGrammarsInstance) x with
  | some i => decide (WellFormed i ∧ StructuralInequivalenceUnaryLinearGrammarsFeasible i)
  | none => false

/-- **STRUCTURAL INEQUIVALENCE FOR LINEAR GRAMMARS over a one-letter alphabet is
NP-complete.** Source: Garey and Johnson (1979), [AL13], comment; Hunt, Rosenkrantz and
Szymanski (1976). -/
public theorem_wanted structuralInequivalenceUnaryLinearGrammars_npComplete :
    structuralInequivalenceUnaryLinearGrammarsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L structuralInequivalenceUnaryLinearGrammarsDec

end MetaMathlibExt.Complexity.NPComplete.StructuralInequivalenceUnaryLinearGrammars
